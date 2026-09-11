import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyEightCRFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyEightCRFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyEightCRFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyEightCRFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyEightCRFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyEightCRFastPow a n * ninetyEightCRFastPow a n * a else ninetyEightCRFastPow a n * ninetyEightCRFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyEightCR_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyEightCR_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyEightCR_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyEightCR_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyEightCR_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyEightCR_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyEightCR_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyEightCR_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyEightCR_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyEightCR_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyEightCR_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyEightCR_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyEightCR_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyEightCR_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyEightCR_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyEightCR_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyEightCR_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyEightCR_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyEightCR_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyEightCR_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyEightCR_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyEightCR_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyEightCR_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyEightCR_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyEightCR_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyEightCR_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyEightCR_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyEightCR_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyEightCR_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyEightCR_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyEightCR_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyEightCR_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyEightCR_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyEightCR_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyEightCR_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyEightCR_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyEightCR_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyEightCR_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyEightCR_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyEightCR_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyEightCR_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyEightCR_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyEightCR_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyEightCR_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyEightCR_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetyEightCR_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyEightCR_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyEightCR_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyEightCR_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyEightCR_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyEightCR_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyEightCR_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetyEightCR_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyEightCR_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetyEightCR_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyEightCR_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetyEightCR_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyEightCR_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyEightCR_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyEightCR_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetyEightCR_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyEightCR_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyEightCR_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyEightCR_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetyEightCR_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetyEightCR_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyEightCR_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetyEightCR_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetyEightCR_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyEightCR_421 : Nat.Prime 421 := by norm_num

private theorem prime_ninetyEightCR_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetyEightCR_433 : Nat.Prime 433 := by norm_num

private theorem prime_ninetyEightCR_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyEightCR_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyEightCR_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyEightCR_467 : Nat.Prime 467 := by norm_num

private theorem prime_ninetyEightCR_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetyEightCR_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyEightCR_503 : Nat.Prime 503 := by norm_num

private theorem prime_ninetyEightCR_541 : Nat.Prime 541 := by norm_num

private theorem prime_ninetyEightCR_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetyEightCR_577 : Nat.Prime 577 := by norm_num

private theorem prime_ninetyEightCR_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetyEightCR_619 : Nat.Prime 619 := by norm_num

private theorem prime_ninetyEightCR_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetyEightCR_653 : Nat.Prime 653 := by norm_num

private theorem prime_ninetyEightCR_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetyEightCR_661 : Nat.Prime 661 := by norm_num

private theorem prime_ninetyEightCR_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetyEightCR_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetyEightCR_733 : Nat.Prime 733 := by norm_num

private theorem prime_ninetyEightCR_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyEightCR_761 : Nat.Prime 761 := by norm_num

private theorem prime_ninetyEightCR_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetyEightCR_839 : Nat.Prime 839 := by norm_num

private theorem prime_ninetyEightCR_877 : Nat.Prime 877 := by norm_num

private theorem prime_ninetyEightCR_881 : Nat.Prime 881 := by norm_num

private theorem prime_ninetyEightCR_911 : Nat.Prime 911 := by norm_num

private theorem prime_ninetyEightCR_919 : Nat.Prime 919 := by norm_num

private theorem prime_ninetyEightCR_937 : Nat.Prime 937 := by norm_num

private theorem prime_ninetyEightCR_941 : Nat.Prime 941 := by norm_num

private theorem prime_ninetyEightCR_991 : Nat.Prime 991 := by norm_num

private theorem prime_ninetyEightCR_997 : Nat.Prime 997 := by norm_num

private theorem prime_ninetyEightCR_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_ninetyEightCR_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_ninetyEightCR_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_ninetyEightCR_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_ninetyEightCR_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_ninetyEightCR_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyEightCR_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_ninetyEightCR_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetyEightCR_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_ninetyEightCR_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_ninetyEightCR_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_ninetyEightCR_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_ninetyEightCR_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_ninetyEightCR_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_ninetyEightCR_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_ninetyEightCR_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_ninetyEightCR_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_ninetyEightCR_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_ninetyEightCR_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetyEightCR_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_ninetyEightCR_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_ninetyEightCR_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_ninetyEightCR_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_ninetyEightCR_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_ninetyEightCR_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_ninetyEightCR_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_ninetyEightCR_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_ninetyEightCR_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_ninetyEightCR_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_ninetyEightCR_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_ninetyEightCR_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_ninetyEightCR_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_ninetyEightCR_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_ninetyEightCR_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_ninetyEightCR_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_ninetyEightCR_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_ninetyEightCR_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_ninetyEightCR_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_ninetyEightCR_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_ninetyEightCR_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_ninetyEightCR_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_ninetyEightCR_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_ninetyEightCR_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_ninetyEightCR_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_ninetyEightCR_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_ninetyEightCR_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_ninetyEightCR_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_ninetyEightCR_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_ninetyEightCR_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_ninetyEightCR_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_ninetyEightCR_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_ninetyEightCR_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_ninetyEightCR_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_ninetyEightCR_3187 : Nat.Prime 3187 := by norm_num

private theorem prime_ninetyEightCR_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_ninetyEightCR_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_ninetyEightCR_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_ninetyEightCR_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_ninetyEightCR_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_ninetyEightCR_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_ninetyEightCR_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_ninetyEightCR_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_ninetyEightCR_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_ninetyEightCR_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_ninetyEightCR_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_ninetyEightCR_4229 : Nat.Prime 4229 := by norm_num

private theorem prime_ninetyEightCR_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_ninetyEightCR_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_ninetyEightCR_4861 : Nat.Prime 4861 := by norm_num

private theorem prime_ninetyEightCR_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_ninetyEightCR_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_ninetyEightCR_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_ninetyEightCR_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_ninetyEightCR_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_ninetyEightCR_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_ninetyEightCR_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_ninetyEightCR_5179 : Nat.Prime 5179 := by norm_num

private theorem prime_ninetyEightCR_5347 : Nat.Prime 5347 := by norm_num

private theorem prime_ninetyEightCR_5381 : Nat.Prime 5381 := by norm_num

private theorem prime_ninetyEightCR_5393 : Nat.Prime 5393 := by norm_num

private theorem prime_ninetyEightCR_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_ninetyEightCR_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_ninetyEightCR_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_ninetyEightCR_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_ninetyEightCR_6163 : Nat.Prime 6163 := by norm_num

private theorem prime_ninetyEightCR_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_ninetyEightCR_6301 : Nat.Prime 6301 := by norm_num

private theorem prime_ninetyEightCR_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_ninetyEightCR_6421 : Nat.Prime 6421 := by norm_num

private theorem prime_ninetyEightCR_6653 : Nat.Prime 6653 := by norm_num

private theorem prime_ninetyEightCR_6857 : Nat.Prime 6857 := by norm_num

private theorem prime_ninetyEightCR_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_ninetyEightCR_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_ninetyEightCR_7457 : Nat.Prime 7457 := by norm_num

private theorem prime_ninetyEightCR_7529 : Nat.Prime 7529 := by norm_num

private theorem prime_ninetyEightCR_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_ninetyEightCR_8017 : Nat.Prime 8017 := by norm_num

private theorem prime_ninetyEightCR_8467 : Nat.Prime 8467 := by norm_num

private theorem prime_ninetyEightCR_8677 : Nat.Prime 8677 := by norm_num

private theorem prime_ninetyEightCR_9791 : Nat.Prime 9791 := by norm_num

private theorem prime_ninetyEightCR_9923 : Nat.Prime 9923 := by norm_num

private theorem prime_ninetyEightCR_10771 : Nat.Prime 10771 := by norm_num

private theorem prime_ninetyEightCR_11447 : Nat.Prime 11447 := by norm_num

private theorem prime_ninetyEightCR_11779 : Nat.Prime 11779 := by norm_num

private theorem prime_ninetyEightCR_12239 : Nat.Prime 12239 := by norm_num

private theorem prime_ninetyEightCR_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_ninetyEightCR_13219 : Nat.Prime 13219 := by norm_num

private theorem prime_ninetyEightCR_13249 : Nat.Prime 13249 := by norm_num

private theorem prime_ninetyEightCR_13451 : Nat.Prime 13451 := by norm_num

private theorem prime_ninetyEightCR_13523 : Nat.Prime 13523 := by norm_num

private theorem prime_ninetyEightCR_13553 : Nat.Prime 13553 := by norm_num

private theorem prime_ninetyEightCR_13613 : Nat.Prime 13613 := by norm_num

private theorem prime_ninetyEightCR_13679 : Nat.Prime 13679 := by norm_num

private theorem prime_ninetyEightCR_14071 : Nat.Prime 14071 := by norm_num

private theorem prime_ninetyEightCR_14813 : Nat.Prime 14813 := by norm_num

private theorem prime_ninetyEightCR_15193 : Nat.Prime 15193 := by norm_num

private theorem prime_ninetyEightCR_15649 : Nat.Prime 15649 := by norm_num

private theorem prime_ninetyEightCR_15773 : Nat.Prime 15773 := by norm_num

private theorem prime_ninetyEightCR_16553 : Nat.Prime 16553 := by norm_num

private theorem prime_ninetyEightCR_16993 : Nat.Prime 16993 := by norm_num

private theorem prime_ninetyEightCR_17903 : Nat.Prime 17903 := by norm_num

private theorem prime_ninetyEightCR_18013 : Nat.Prime 18013 := by norm_num

private theorem prime_ninetyEightCR_18869 : Nat.Prime 18869 := by norm_num

private theorem prime_ninetyEightCR_19087 : Nat.Prime 19087 := by norm_num

private theorem prime_ninetyEightCR_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_ninetyEightCR_19949 : Nat.Prime 19949 := by norm_num

private theorem prime_ninetyEightCR_20149 : Nat.Prime 20149 := by norm_num

private theorem prime_ninetyEightCR_20717 : Nat.Prime 20717 := by norm_num

private theorem prime_ninetyEightCR_21193 : Nat.Prime 21193 := by norm_num

private theorem prime_ninetyEightCR_23189 : Nat.Prime 23189 := by norm_num

private theorem prime_ninetyEightCR_23197 : Nat.Prime 23197 := by norm_num

private theorem prime_ninetyEightCR_23431 : Nat.Prime 23431 := by norm_num

private theorem prime_ninetyEightCR_24019 : Nat.Prime 24019 := by norm_num

private theorem prime_ninetyEightCR_24133 : Nat.Prime 24133 := by norm_num

private theorem prime_ninetyEightCR_26237 : Nat.Prime 26237 := by norm_num

private theorem prime_ninetyEightCR_27061 : Nat.Prime 27061 := by norm_num

private theorem prime_ninetyEightCR_29167 : Nat.Prime 29167 := by norm_num

private theorem prime_ninetyEightCR_29569 : Nat.Prime 29569 := by norm_num

private theorem prime_ninetyEightCR_30091 : Nat.Prime 30091 := by norm_num

private theorem prime_ninetyEightCR_30539 : Nat.Prime 30539 := by norm_num

private theorem prime_ninetyEightCR_31583 : Nat.Prime 31583 := by norm_num

private theorem prime_ninetyEightCR_32191 : Nat.Prime 32191 := by norm_num

private theorem prime_ninetyEightCR_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_ninetyEightCR_32797 : Nat.Prime 32797 := by norm_num

private theorem prime_ninetyEightCR_32839 : Nat.Prime 32839 := by norm_num

private theorem prime_ninetyEightCR_33247 : Nat.Prime 33247 := by norm_num

private theorem prime_ninetyEightCR_33857 : Nat.Prime 33857 := by norm_num

private theorem prime_ninetyEightCR_35051 : Nat.Prime 35051 := by norm_num

private theorem prime_ninetyEightCR_38977 : Nat.Prime 38977 := by norm_num

private theorem prime_ninetyEightCR_40433 : Nat.Prime 40433 := by norm_num

private theorem prime_ninetyEightCR_40823 : Nat.Prime 40823 := by norm_num

private theorem prime_ninetyEightCR_42709 : Nat.Prime 42709 := by norm_num

private theorem prime_ninetyEightCR_43613 : Nat.Prime 43613 := by norm_num

private theorem prime_ninetyEightCR_46237 : Nat.Prime 46237 := by norm_num

private theorem prime_ninetyEightCR_46273 : Nat.Prime 46273 := by norm_num

private theorem prime_ninetyEightCR_48731 : Nat.Prime 48731 := by norm_num

private theorem prime_ninetyEightCR_49369 : Nat.Prime 49369 := by norm_num

private theorem prime_ninetyEightCR_50873 : Nat.Prime 50873 := by norm_num

private theorem prime_ninetyEightCR_53453 : Nat.Prime 53453 := by norm_num

private theorem prime_ninetyEightCR_53987 : Nat.Prime 53987 := by norm_num

private theorem prime_ninetyEightCR_56197 : Nat.Prime 56197 := by norm_num

private theorem prime_ninetyEightCR_58073 : Nat.Prime 58073 := by norm_num

private theorem prime_ninetyEightCR_58687 : Nat.Prime 58687 := by norm_num

private theorem prime_ninetyEightCR_59183 : Nat.Prime 59183 := by norm_num

private theorem prime_ninetyEightCR_60937 : Nat.Prime 60937 := by norm_num

private theorem prime_ninetyEightCR_61151 : Nat.Prime 61151 := by norm_num

private theorem prime_ninetyEightCR_61357 : Nat.Prime 61357 := by norm_num

private theorem prime_ninetyEightCR_66541 : Nat.Prime 66541 := by norm_num

private theorem prime_ninetyEightCR_69677 : Nat.Prime 69677 := by norm_num

private theorem prime_ninetyEightCR_74219 : Nat.Prime 74219 := by norm_num

private theorem prime_ninetyEightCR_75931 : Nat.Prime 75931 := by norm_num

private theorem prime_ninetyEightCR_77351 : Nat.Prime 77351 := by norm_num

private theorem prime_ninetyEightCR_79687 : Nat.Prime 79687 := by norm_num

private theorem prime_ninetyEightCR_79817 : Nat.Prime 79817 := by norm_num

private theorem prime_ninetyEightCR_83921 : Nat.Prime 83921 := by norm_num

private theorem prime_ninetyEightCR_84947 : Nat.Prime 84947 := by norm_num

private theorem prime_ninetyEightCR_86171 : Nat.Prime 86171 := by norm_num

private theorem prime_ninetyEightCR_86729 : Nat.Prime 86729 := by norm_num

private theorem prime_ninetyEightCR_86813 : Nat.Prime 86813 := by norm_num

private theorem prime_ninetyEightCR_87083 : Nat.Prime 87083 := by norm_num

private theorem prime_ninetyEightCR_90031 : Nat.Prime 90031 := by norm_num

private theorem prime_ninetyEightCR_90617 : Nat.Prime 90617 := by norm_num

private theorem prime_ninetyEightCR_92921 : Nat.Prime 92921 := by norm_num

private theorem prime_ninetyEightCR_96377 : Nat.Prime 96377 := by norm_num

private theorem prime_ninetyEightCR_97001 : Nat.Prime 97001 := by norm_num

private theorem prime_ninetyEightCR_104287 : Nat.Prime 104287 := by norm_num

private theorem prime_ninetyEightCR_104473 : Nat.Prime 104473 := by norm_num

private theorem prime_ninetyEightCR_105733 : Nat.Prime 105733 := by norm_num

private theorem prime_ninetyEightCR_109913 : Nat.Prime 109913 := by norm_num

private theorem prime_ninetyEightCR_110777 : Nat.Prime 110777 := by norm_num

private theorem prime_ninetyEightCR_111373 : Nat.Prime 111373 := by norm_num

private theorem prime_ninetyEightCR_116437 : Nat.Prime 116437 := by norm_num

private theorem prime_ninetyEightCR_119291 : Nat.Prime 119291 := by norm_num

private theorem prime_ninetyEightCR_120157 : Nat.Prime 120157 := by norm_num

private theorem prime_ninetyEightCR_120941 : Nat.Prime 120941 := by norm_num

private theorem prime_ninetyEightCR_122231 : Nat.Prime 122231 := by norm_num

private theorem prime_ninetyEightCR_130651 : Nat.Prime 130651 := by norm_num

private theorem prime_ninetyEightCR_137993 : Nat.Prime 137993 := by norm_num

private theorem prime_ninetyEightCR_145193 : Nat.Prime 145193 := by norm_num

private theorem prime_ninetyEightCR_149251 : Nat.Prime 149251 := by norm_num

private theorem prime_ninetyEightCR_152311 : Nat.Prime 152311 := by norm_num

private theorem prime_ninetyEightCR_153107 : Nat.Prime 153107 := by norm_num

private theorem prime_ninetyEightCR_154127 : Nat.Prime 154127 := by norm_num

private theorem prime_ninetyEightCR_155461 : Nat.Prime 155461 := by norm_num

private theorem prime_ninetyEightCR_172721 : Nat.Prime 172721 := by norm_num

private theorem prime_ninetyEightCR_173651 : Nat.Prime 173651 := by norm_num

private theorem prime_ninetyEightCR_175433 : Nat.Prime 175433 := by norm_num

private theorem prime_ninetyEightCR_176537 : Nat.Prime 176537 := by norm_num

private theorem prime_ninetyEightCR_176609 : Nat.Prime 176609 := by norm_num

private theorem prime_ninetyEightCR_178037 : Nat.Prime 178037 := by norm_num

private theorem prime_ninetyEightCR_188827 : Nat.Prime 188827 := by norm_num

private theorem prime_ninetyEightCR_204719 : Nat.Prime 204719 := by norm_num

private theorem prime_ninetyEightCR_205507 : Nat.Prime 205507 := by norm_num

private theorem prime_ninetyEightCR_207287 : Nat.Prime 207287 := by norm_num

private theorem prime_ninetyEightCR_209227 : Nat.Prime 209227 := by norm_num

private theorem prime_ninetyEightCR_211271 : Nat.Prime 211271 := by norm_num

private theorem prime_ninetyEightCR_212167 : Nat.Prime 212167 := by norm_num

private theorem prime_ninetyEightCR_217909 : Nat.Prime 217909 := by norm_num

private theorem prime_ninetyEightCR_217979 : Nat.Prime 217979 := by norm_num

private theorem prime_ninetyEightCR_227519 : Nat.Prime 227519 := by norm_num

private theorem prime_ninetyEightCR_229627 : Nat.Prime 229627 := by norm_num

private theorem prime_ninetyEightCR_233609 : Nat.Prime 233609 := by norm_num

private theorem prime_ninetyEightCR_243533 : Nat.Prime 243533 := by norm_num

private theorem prime_ninetyEightCR_244243 : Nat.Prime 244243 := by norm_num

private theorem prime_ninetyEightCR_258631 : Nat.Prime 258631 := by norm_num

private theorem prime_ninetyEightCR_268729 : Nat.Prime 268729 := by norm_num

private theorem prime_ninetyEightCR_279557 : Nat.Prime 279557 := by norm_num

private theorem prime_ninetyEightCR_322969 : Nat.Prime 322969 := by norm_num

private theorem prime_ninetyEightCR_324647 : Nat.Prime 324647 := by norm_num

private theorem prime_ninetyEightCR_329473 : Nat.Prime 329473 := by norm_num

private theorem prime_ninetyEightCR_338707 : Nat.Prime 338707 := by norm_num

private theorem prime_ninetyEightCR_353819 : Nat.Prime 353819 := by norm_num

private theorem prime_ninetyEightCR_374641 : Nat.Prime 374641 := by norm_num

private theorem prime_ninetyEightCR_374719 : Nat.Prime 374719 := by norm_num

private theorem prime_ninetyEightCR_376297 : Nat.Prime 376297 := by norm_num

private theorem prime_ninetyEightCR_383321 : Nat.Prime 383321 := by norm_num

private theorem prime_ninetyEightCR_400069 : Nat.Prime 400069 := by norm_num

private theorem prime_ninetyEightCR_440203 : Nat.Prime 440203 := by norm_num

private theorem prime_ninetyEightCR_468953 : Nat.Prime 468953 := by norm_num

private theorem prime_ninetyEightCR_479623 : Nat.Prime 479623 := by norm_num

private theorem prime_ninetyEightCR_514531 : Nat.Prime 514531 := by norm_num

private theorem prime_ninetyEightCR_526069 : Nat.Prime 526069 := by norm_num

private theorem prime_ninetyEightCR_527237 : Nat.Prime 527237 := by norm_num

private theorem prime_ninetyEightCR_531263 : Nat.Prime 531263 := by norm_num

private theorem prime_ninetyEightCR_531833 : Nat.Prime 531833 := by norm_num

private theorem prime_ninetyEightCR_536671 : Nat.Prime 536671 := by norm_num

private theorem prime_ninetyEightCR_550651 : Nat.Prime 550651 := by norm_num

private theorem prime_ninetyEightCR_563851 : Nat.Prime 563851 := by norm_num

private theorem prime_ninetyEightCR_576701 : Nat.Prime 576701 := by norm_num

private theorem prime_ninetyEightCR_615761 : Nat.Prime 615761 := by norm_num

private theorem prime_ninetyEightCR_628183 : Nat.Prime 628183 := by norm_num

private theorem prime_ninetyEightCR_671299 : Nat.Prime 671299 := by norm_num

private theorem prime_ninetyEightCR_685429 : Nat.Prime 685429 := by norm_num

private theorem prime_ninetyEightCR_711499 : Nat.Prime 711499 := by norm_num

private theorem prime_ninetyEightCR_713753 : Nat.Prime 713753 := by norm_num

private theorem prime_ninetyEightCR_723923 : Nat.Prime 723923 := by norm_num

private theorem prime_ninetyEightCR_797833 : Nat.Prime 797833 := by norm_num

private theorem prime_ninetyEightCR_803587 : Nat.Prime 803587 := by norm_num

private theorem prime_ninetyEightCR_850043 : Nat.Prime 850043 := by norm_num

private theorem prime_ninetyEightCR_902029 : Nat.Prime 902029 := by norm_num

private theorem prime_ninetyEightCR_906541 : Nat.Prime 906541 := by norm_num

private theorem prime_ninetyEightCR_946411 : Nat.Prime 946411 := by norm_num

private theorem prime_ninetyEightCR_963427 : Nat.Prime 963427 := by norm_num

private theorem prime_ninetyEightCR_965201 : Nat.Prime 965201 := by norm_num

private theorem prime_ninetyEightCR_991927 : Nat.Prime 991927 := by norm_num

private theorem prime_ninetyEightCR_1092173 : Nat.Prime 1092173 := by norm_num

private theorem prime_ninetyEightCR_1131763 : Nat.Prime 1131763 := by norm_num

private theorem prime_ninetyEightCR_1230829 : Nat.Prime 1230829 := by norm_num

private theorem prime_ninetyEightCR_1301879 : Nat.Prime 1301879 := by norm_num

private theorem prime_ninetyEightCR_1315007 : Nat.Prime 1315007 := by norm_num

private theorem prime_ninetyEightCR_1397131 : Nat.Prime 1397131 := by norm_num

private theorem prime_ninetyEightCR_1579639 : Nat.Prime 1579639 := by norm_num

private theorem prime_ninetyEightCR_1580851 : Nat.Prime 1580851 := by norm_num

private theorem prime_ninetyEightCR_1669219 : Nat.Prime 1669219 := by norm_num

private theorem prime_ninetyEightCR_1677089 : Nat.Prime 1677089 := by norm_num

private theorem prime_ninetyEightCR_1774901 : Nat.Prime 1774901 := by norm_num

private theorem prime_ninetyEightCR_1804007 : Nat.Prime 1804007 := by norm_num

private theorem prime_ninetyEightCR_2070953 : Nat.Prime 2070953 := by norm_num

private theorem prime_ninetyEightCR_2238631 : Nat.Prime 2238631 := by norm_num

private theorem prime_ninetyEightCR_2277083 : Nat.Prime 2277083 := by norm_num

private theorem prime_ninetyEightCR_2827679 : Nat.Prime 2827679 := by norm_num

private theorem prime_ninetyEightCR_2851799 : Nat.Prime 2851799 := by norm_num

private theorem prime_ninetyEightCR_2865659 : Nat.Prime 2865659 := by norm_num

private theorem prime_ninetyEightCR_3012913 : Nat.Prime 3012913 := by norm_num

private theorem prime_ninetyEightCR_3052783 : Nat.Prime 3052783 := by norm_num

private theorem prime_ninetyEightCR_3159461 : Nat.Prime 3159461 := by norm_num

private theorem prime_ninetyEightCR_3206363 : Nat.Prime 3206363 := by norm_num

private theorem prime_ninetyEightCR_3244277 : Nat.Prime 3244277 := by norm_num

private theorem prime_ninetyEightCR_3267193 : Nat.Prime 3267193 := by norm_num

private theorem prime_ninetyEightCR_3310357 : Nat.Prime 3310357 := by norm_num

private theorem prime_ninetyEightCR_3336643 : Nat.Prime 3336643 := by norm_num

private theorem prime_ninetyEightCR_3399041 : Nat.Prime 3399041 := by norm_num

private theorem prime_ninetyEightCR_3526147 : Nat.Prime 3526147 := by norm_num

private theorem prime_ninetyEightCR_3574657 : Nat.Prime 3574657 := by norm_num

private theorem prime_ninetyEightCR_3835613 : Nat.Prime 3835613 := by norm_num

private theorem prime_ninetyEightCR_3837017 : Nat.Prime 3837017 := by norm_num

private theorem prime_ninetyEightCR_3885461 : Nat.Prime 3885461 := by norm_num

private theorem prime_ninetyEightCR_4063711 : Nat.Prime 4063711 := by norm_num

private theorem prime_ninetyEightCR_4083701 : Nat.Prime 4083701 := by norm_num

private theorem prime_ninetyEightCR_4326383 : Nat.Prime 4326383 := by norm_num

private theorem prime_ninetyEightCR_4367863 : Nat.Prime 4367863 := by norm_num

private theorem prime_ninetyEightCR_4374571 : Nat.Prime 4374571 := by norm_num

private theorem prime_ninetyEightCR_4698101 : Nat.Prime 4698101 := by norm_num

private theorem prime_ninetyEightCR_4849049 : Nat.Prime 4849049 := by norm_num

private theorem prime_ninetyEightCR_4908481 : Nat.Prime 4908481 := by norm_num

private theorem prime_ninetyEightCR_4933843 : Nat.Prime 4933843 := by norm_num

private theorem prime_ninetyEightCR_5077789 : Nat.Prime 5077789 := by norm_num

private theorem prime_ninetyEightCR_5134487 : Nat.Prime 5134487 := by norm_num

private theorem prime_ninetyEightCR_5984453 : Nat.Prime 5984453 := by norm_num

private theorem prime_ninetyEightCR_6113273 : Nat.Prime 6113273 := by norm_num

private theorem prime_ninetyEightCR_6582463 : Nat.Prime 6582463 := by norm_num

private theorem prime_ninetyEightCR_7804171 : Nat.Prime 7804171 := by norm_num

private theorem prime_ninetyEightCR_7927747 : Nat.Prime 7927747 := by norm_num

private theorem prime_ninetyEightCR_8008009 : Nat.Prime 8008009 := by norm_num

private theorem prime_ninetyEightCR_8656283 : Nat.Prime 8656283 := by norm_num

private theorem prime_ninetyEightCR_9263983 : Nat.Prime 9263983 := by norm_num

private theorem prime_ninetyEightCR_9281809 : Nat.Prime 9281809 := by norm_num

private theorem prime_ninetyEightCR_9753209 : Nat.Prime 9753209 := by norm_num

private theorem prime_ninetyEightCR_10118377 : Nat.Prime 10118377 := by norm_num

private theorem prime_ninetyEightCR_10483717 : Nat.Prime 10483717 := by norm_num

private theorem prime_ninetyEightCR_10589333 : Nat.Prime 10589333 := by norm_num

private theorem prime_ninetyEightCR_10597127 : Nat.Prime 10597127 := by norm_num

private theorem prime_ninetyEightCR_11074697 : Nat.Prime 11074697 := by norm_num

private theorem prime_ninetyEightCR_11391427 : Nat.Prime 11391427 := by norm_num

private theorem prime_ninetyEightCR_13029823 : Nat.Prime 13029823 := by norm_num

private theorem prime_ninetyEightCR_13590601 : Nat.Prime 13590601 := by norm_num

private theorem prime_ninetyEightCR_14945531 : Nat.Prime 14945531 := by norm_num

private theorem prime_ninetyEightCR_14967427 : Nat.Prime 14967427 := by norm_num

private theorem prime_ninetyEightCR_15280393 : Nat.Prime 15280393 := by norm_num

private theorem prime_ninetyEightCR_15903637 : Nat.Prime 15903637 := by norm_num

private theorem prime_ninetyEightCR_16110221 : Nat.Prime 16110221 := by norm_num

private theorem prime_ninetyEightCR_17156057 : Nat.Prime 17156057 := by norm_num

private theorem prime_ninetyEightCR_17276977 : Nat.Prime 17276977 := by norm_num

private theorem prime_ninetyEightCR_18653309 : Nat.Prime 18653309 := by norm_num

private theorem prime_ninetyEightCR_19976591 : Nat.Prime 19976591 := by norm_num

private theorem prime_ninetyEightCR_20454647 : Nat.Prime 20454647 := by norm_num

private theorem prime_ninetyEightCR_21338477 : Nat.Prime 21338477 := by norm_num

private theorem prime_ninetyEightCR_21743507 : Nat.Prime 21743507 := by norm_num

private theorem prime_ninetyEightCR_23353331 : Nat.Prime 23353331 := by norm_num

private theorem prime_ninetyEightCR_23386289 : Nat.Prime 23386289 := by norm_num

private theorem prime_ninetyEightCR_25041431 : Nat.Prime 25041431 := by norm_num

private theorem prime_ninetyEightCR_25106231 : Nat.Prime 25106231 := by norm_num

private theorem prime_ninetyEightCR_25118851 : Nat.Prime 25118851 := by norm_num

private theorem prime_ninetyEightCR_28466947 : Nat.Prime 28466947 := by norm_num

private theorem prime_ninetyEightCR_34263071 : Nat.Prime 34263071 := by
  apply lucas_primality 34263071 (26 : ZMod 34263071)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (58073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (58073, 1)] : List FactorBlock).map factorBlockValue).prod) = 34263071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_59
      · exact prime_ninetyEightCR_58073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 34263071) ^ 17131535 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 34263071) ^ 6852614 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 34263071) ^ 580730 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 34263071) ^ 590 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_35773813 : Nat.Prime 35773813 := by
  apply lucas_primality 35773813 (2 : ZMod 35773813)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (41, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (41, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 35773813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_41
      · exact prime_ninetyEightCR_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35773813) ^ 17886906 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 35773813) ^ 11924604 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 35773813) ^ 872532 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 35773813) ^ 13284 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_42117227 : Nat.Prime 42117227 := by
  apply lucas_primality 42117227 (2 : ZMod 42117227)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (7529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (7529, 1)] : List FactorBlock).map factorBlockValue).prod) = 42117227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_2797
      · exact prime_ninetyEightCR_7529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42117227) ^ 21058613 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42117227) ^ 15058 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 42117227) ^ 5594 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_44263829 : Nat.Prime 44263829 := by
  apply lucas_primality 44263829 (2 : ZMod 44263829)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1580851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1580851, 1)] : List FactorBlock).map factorBlockValue).prod) = 44263829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_1580851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44263829) ^ 22131914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44263829) ^ 6323404 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 44263829) ^ 28 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_45331291 : Nat.Prime 45331291 := by
  apply lucas_primality 45331291 (3 : ZMod 45331291)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (13613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (13613, 1)] : List FactorBlock).map factorBlockValue).prod) = 45331291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_13613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45331291) ^ 22665645 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45331291) ^ 15110430 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45331291) ^ 9066258 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45331291) ^ 1225170 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 45331291) ^ 3330 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_47107699 : Nat.Prime 47107699 := by
  apply lucas_primality 47107699 (2 : ZMod 47107699)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (713753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (713753, 1)] : List FactorBlock).map factorBlockValue).prod) = 47107699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_713753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47107699) ^ 23553849 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107699) ^ 15702566 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107699) ^ 4282518 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 47107699) ^ 66 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_48333529 : Nat.Prime 48333529 := by
  apply lucas_primality 48333529 (7 : ZMod 48333529)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (671299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (671299, 1)] : List FactorBlock).map factorBlockValue).prod) = 48333529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_671299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 48333529) ^ 24166764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48333529) ^ 16111176 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 48333529) ^ 72 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_48725311 : Nat.Prime 48725311 := by
  apply lucas_primality 48725311 (6 : ZMod 48725311)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (73, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (73, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 48725311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_73
      · exact prime_ninetyEightCR_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 48725311) ^ 24362655 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 48725311) ^ 16241770 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 48725311) ^ 9745062 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 48725311) ^ 2564490 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 48725311) ^ 667470 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 48725311) ^ 41610 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_49338431 : Nat.Prime 49338431 := by
  apply lucas_primality 49338431 (7 : ZMod 49338431)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4933843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4933843, 1)] : List FactorBlock).map factorBlockValue).prod) = 49338431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_4933843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 49338431) ^ 24669215 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 49338431) ^ 9867686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 49338431) ^ 10 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_51136157 : Nat.Prime 51136157 := by
  apply lucas_primality 51136157 (2 : ZMod 51136157)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (157, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (157, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 51136157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_107
      · exact prime_ninetyEightCR_157
      · exact prime_ninetyEightCR_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51136157) ^ 25568078 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51136157) ^ 477908 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51136157) ^ 325708 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 51136157) ^ 67196 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_52275089 : Nat.Prime 52275089 := by
  apply lucas_primality 52275089 (3 : ZMod 52275089)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3267193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3267193, 1)] : List FactorBlock).map factorBlockValue).prod) = 52275089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3267193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 52275089) ^ 26137544 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 52275089) ^ 16 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_53088947 : Nat.Prime 53088947 := by
  apply lucas_primality 53088947 (2 : ZMod 53088947)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4933, 1), (5381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4933, 1), (5381, 1)] : List FactorBlock).map factorBlockValue).prod) = 53088947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_4933
      · exact prime_ninetyEightCR_5381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 53088947) ^ 26544473 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 53088947) ^ 10762 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 53088947) ^ 9866 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_55688233 : Nat.Prime 55688233 := by
  apply lucas_primality 55688233 (5 : ZMod 55688233)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (49369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (49369, 1)] : List FactorBlock).map factorBlockValue).prod) = 55688233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_47
      · exact prime_ninetyEightCR_49369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55688233) ^ 27844116 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 55688233) ^ 18562744 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 55688233) ^ 1184856 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 55688233) ^ 1128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_55689259 : Nat.Prime 55689259 := by
  apply lucas_primality 55689259 (3 : ZMod 55689259)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (104287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (104287, 1)] : List FactorBlock).map factorBlockValue).prod) = 55689259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_89
      · exact prime_ninetyEightCR_104287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 55689259) ^ 27844629 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 55689259) ^ 18563086 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 55689259) ^ 625722 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 55689259) ^ 534 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_57650561 : Nat.Prime 57650561 := by
  apply lucas_primality 57650561 (3 : ZMod 57650561)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (11, 1), (19, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (11, 1), (19, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 57650561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 57650561) ^ 28825280 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 57650561) ^ 11530112 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 57650561) ^ 5240960 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 57650561) ^ 3034240 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 57650561) ^ 133760 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_63546409 : Nat.Prime 63546409 := by
  apply lucas_primality 63546409 (7 : ZMod 63546409)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (193, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (193, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 63546409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_193
      · exact prime_ninetyEightCR_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 63546409) ^ 31773204 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63546409) ^ 21182136 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63546409) ^ 3738024 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63546409) ^ 329256 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 63546409) ^ 236232 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_63561161 : Nat.Prime 63561161 := by
  apply lucas_primality 63561161 (3 : ZMod 63561161)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (31, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (31, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) = 63561161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_3943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63561161) ^ 31780580 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63561161) ^ 12712232 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63561161) ^ 4889320 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63561161) ^ 2050360 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 63561161) ^ 16120 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_70715657 : Nat.Prime 70715657 := by
  apply lucas_primality 70715657 (3 : ZMod 70715657)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (803587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (803587, 1)] : List FactorBlock).map factorBlockValue).prod) = 70715657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_803587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 70715657) ^ 35357828 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70715657) ^ 6428696 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 70715657) ^ 88 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_85216757 : Nat.Prime 85216757 := by
  apply lucas_primality 85216757 (2 : ZMod 85216757)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (71, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (71, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) = 85216757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_61
      · exact prime_ninetyEightCR_71
      · exact prime_ninetyEightCR_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85216757) ^ 42608378 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85216757) ^ 1396996 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85216757) ^ 1200236 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 85216757) ^ 17324 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_88158337 : Nat.Prime 88158337 := by
  apply lucas_primality 88158337 (5 : ZMod 88158337)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (32797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (32797, 1)] : List FactorBlock).map factorBlockValue).prod) = 88158337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_32797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 88158337) ^ 44079168 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 88158337) ^ 29386112 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 88158337) ^ 12594048 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 88158337) ^ 2688 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_89673187 : Nat.Prime 89673187 := by
  apply lucas_primality 89673187 (5 : ZMod 89673187)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14945531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14945531, 1)] : List FactorBlock).map factorBlockValue).prod) = 89673187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_14945531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 89673187) ^ 44836593 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 89673187) ^ 29891062 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 89673187) ^ 6 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_90365531 : Nat.Prime 90365531 := by
  apply lucas_primality 90365531 (2 : ZMod 90365531)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 2), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 2), (3217, 1)] : List FactorBlock).map factorBlockValue).prod) = 90365531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_53
      · exact prime_ninetyEightCR_3217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90365531) ^ 45182765 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 90365531) ^ 18073106 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 90365531) ^ 1705010 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 90365531) ^ 28090 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_96806953 : Nat.Prime 96806953 := by
  apply lucas_primality 96806953 (7 : ZMod 96806953)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (122231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (122231, 1)] : List FactorBlock).map factorBlockValue).prod) = 96806953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_122231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 96806953) ^ 48403476 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 96806953) ^ 32268984 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 96806953) ^ 8800632 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 96806953) ^ 792 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_105031403 : Nat.Prime 105031403 := by
  apply lucas_primality 105031403 (2 : ZMod 105031403)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (153107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (153107, 1)] : List FactorBlock).map factorBlockValue).prod) = 105031403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_153107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105031403) ^ 52515701 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105031403) ^ 15004486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105031403) ^ 686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_111577399 : Nat.Prime 111577399 := by
  apply lucas_primality 111577399 (3 : ZMod 111577399)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (449, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (449, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 111577399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_83
      · exact prime_ninetyEightCR_449
      · exact prime_ninetyEightCR_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 111577399) ^ 55788699 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 111577399) ^ 37192466 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 111577399) ^ 1344306 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 111577399) ^ 248502 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 111577399) ^ 223602 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_131841631 : Nat.Prime 131841631 := by
  apply lucas_primality 131841631 (3 : ZMod 131841631)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (86171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (86171, 1)] : List FactorBlock).map factorBlockValue).prod) = 131841631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_86171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131841631) ^ 65920815 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 131841631) ^ 43947210 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 131841631) ^ 26368326 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 131841631) ^ 7755390 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 131841631) ^ 1530 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_142902233 : Nat.Prime 142902233 := by
  apply lucas_primality 142902233 (3 : ZMod 142902233)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (599, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (599, 1), (2711, 1)] : List FactorBlock).map factorBlockValue).prod) = 142902233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_599
      · exact prime_ninetyEightCR_2711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 142902233) ^ 71451116 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142902233) ^ 12991112 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142902233) ^ 238568 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142902233) ^ 52712 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_146700929 : Nat.Prime 146700929 := by
  apply lucas_primality 146700929 (3 : ZMod 146700929)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11, 1), (31, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11, 1), (31, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) = 146700929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_3361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 146700929) ^ 73350464 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146700929) ^ 13336448 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146700929) ^ 4732288 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 146700929) ^ 43648 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_148223729 : Nat.Prime 148223729 := by
  apply lucas_primality 148223729 (3 : ZMod 148223729)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (9263983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (9263983, 1)] : List FactorBlock).map factorBlockValue).prod) = 148223729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_9263983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 148223729) ^ 74111864 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 148223729) ^ 16 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_156040069 : Nat.Prime 156040069 := by
  apply lucas_primality 156040069 (2 : ZMod 156040069)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (359, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (359, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 156040069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_359
      · exact prime_ninetyEightCR_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156040069) ^ 78020034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 156040069) ^ 52013356 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 156040069) ^ 5380692 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 156040069) ^ 434652 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 156040069) ^ 124932 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_157364429 : Nat.Prime 157364429 := by
  apply lucas_primality 157364429 (2 : ZMod 157364429)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (743, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (743, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) = 157364429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_743
      · exact prime_ninetyEightCR_4073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157364429) ^ 78682214 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157364429) ^ 12104956 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157364429) ^ 211796 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157364429) ^ 38636 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_164586871 : Nat.Prime 164586871 := by
  apply lucas_primality 164586871 (6 : ZMod 164586871)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (87083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (87083, 1)] : List FactorBlock).map factorBlockValue).prod) = 164586871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_87083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 164586871) ^ 82293435 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 164586871) ^ 54862290 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 164586871) ^ 32917374 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 164586871) ^ 23512410 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 164586871) ^ 1890 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_188430797 : Nat.Prime 188430797 := by
  apply lucas_primality 188430797 (2 : ZMod 188430797)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47107699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47107699, 1)] : List FactorBlock).map factorBlockValue).prod) = 188430797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_47107699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 188430797) ^ 94215398 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 188430797) ^ 4 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_217047199 : Nat.Prime 217047199 := by
  apply lucas_primality 217047199 (3 : ZMod 217047199)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2381, 1), (15193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2381, 1), (15193, 1)] : List FactorBlock).map factorBlockValue).prod) = 217047199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_2381
      · exact prime_ninetyEightCR_15193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 217047199) ^ 108523599 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 217047199) ^ 72349066 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 217047199) ^ 91158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 217047199) ^ 14286 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_222763417 : Nat.Prime 222763417 := by
  apply lucas_primality 222763417 (10 : ZMod 222763417)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9281809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9281809, 1)] : List FactorBlock).map factorBlockValue).prod) = 222763417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_9281809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 222763417) ^ 111381708 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 222763417) ^ 74254472 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 222763417) ^ 24 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_235607089 : Nat.Prime 235607089 := by
  apply lucas_primality 235607089 (19 : ZMod 235607089)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4908481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4908481, 1)] : List FactorBlock).map factorBlockValue).prod) = 235607089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_4908481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 235607089) ^ 117803544 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 235607089) ^ 78535696 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 235607089) ^ 48 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_263392469 : Nat.Prime 263392469 := by
  apply lucas_primality 263392469 (2 : ZMod 263392469)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (902029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (902029, 1)] : List FactorBlock).map factorBlockValue).prod) = 263392469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_73
      · exact prime_ninetyEightCR_902029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 263392469) ^ 131696234 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 263392469) ^ 3608116 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 263392469) ^ 292 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_308809027 : Nat.Prime 308809027 := by
  apply lucas_primality 308809027 (5 : ZMod 308809027)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17156057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17156057, 1)] : List FactorBlock).map factorBlockValue).prod) = 308809027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17156057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 308809027) ^ 154404513 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 308809027) ^ 102936342 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 308809027) ^ 18 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_351197789 : Nat.Prime 351197789 := by
  apply lucas_primality 351197789 (2 : ZMod 351197789)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (911, 1), (96377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (911, 1), (96377, 1)] : List FactorBlock).map factorBlockValue).prod) = 351197789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_911
      · exact prime_ninetyEightCR_96377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 351197789) ^ 175598894 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 351197789) ^ 385508 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 351197789) ^ 3644 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_392850779 : Nat.Prime 392850779 := by
  apply lucas_primality 392850779 (2 : ZMod 392850779)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3347, 1), (58687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3347, 1), (58687, 1)] : List FactorBlock).map factorBlockValue).prod) = 392850779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3347
      · exact prime_ninetyEightCR_58687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 392850779) ^ 196425389 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 392850779) ^ 117374 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 392850779) ^ 6694 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_457924459 : Nat.Prime 457924459 := by
  apply lucas_primality 457924459 (11 : ZMod 457924459)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1774901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1774901, 1)] : List FactorBlock).map factorBlockValue).prod) = 457924459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_43
      · exact prime_ninetyEightCR_1774901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 457924459) ^ 228962229 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 457924459) ^ 152641486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 457924459) ^ 10649406 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 457924459) ^ 258 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_490911529 : Nat.Prime 490911529 := by
  apply lucas_primality 490911529 (7 : ZMod 490911529)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (20454647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (20454647, 1)] : List FactorBlock).map factorBlockValue).prod) = 490911529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_20454647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 490911529) ^ 245455764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 490911529) ^ 163637176 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 490911529) ^ 24 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_507195631 : Nat.Prime 507195631 := by
  apply lucas_primality 507195631 (12 : ZMod 507195631)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (152311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (152311, 1)] : List FactorBlock).map factorBlockValue).prod) = 507195631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_152311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 507195631) ^ 253597815 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (12 : ZMod 507195631) ^ 169065210 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (12 : ZMod 507195631) ^ 101439126 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (12 : ZMod 507195631) ^ 13707990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (12 : ZMod 507195631) ^ 3330 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_556892591 : Nat.Prime 556892591 := by
  apply lucas_primality 556892591 (17 : ZMod 556892591)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (55689259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (55689259, 1)] : List FactorBlock).map factorBlockValue).prod) = 556892591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_55689259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 556892591) ^ 278446295 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 556892591) ^ 111378518 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 556892591) ^ 10 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_616735279 : Nat.Prime 616735279 := by
  apply lucas_primality 616735279 (3 : ZMod 616735279)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (34263071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (34263071, 1)] : List FactorBlock).map factorBlockValue).prod) = 616735279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_34263071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 616735279) ^ 308367639 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 616735279) ^ 205578426 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 616735279) ^ 18 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_635464091 : Nat.Prime 635464091 := by
  apply lucas_primality 635464091 (6 : ZMod 635464091)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (63546409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (63546409, 1)] : List FactorBlock).map factorBlockValue).prod) = 635464091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_63546409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 635464091) ^ 317732045 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 635464091) ^ 127092818 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 635464091) ^ 10 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_673318771 : Nat.Prime 673318771 := by
  apply lucas_primality 673318771 (2 : ZMod 673318771)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (163, 1), (7247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (163, 1), (7247, 1)] : List FactorBlock).map factorBlockValue).prod) = 673318771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_163
      · exact prime_ninetyEightCR_7247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 673318771) ^ 336659385 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 673318771) ^ 224439590 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 673318771) ^ 134663754 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 673318771) ^ 35437830 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 673318771) ^ 4130790 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 673318771) ^ 92910 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_743245259 : Nat.Prime 743245259 := by
  apply lucas_primality 743245259 (2 : ZMod 743245259)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53088947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53088947, 1)] : List FactorBlock).map factorBlockValue).prod) = 743245259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_53088947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 743245259) ^ 371622629 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 743245259) ^ 106177894 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 743245259) ^ 14 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_758270641 : Nat.Prime 758270641 := by
  apply lucas_primality 758270641 (17 : ZMod 758270641)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (3159461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (3159461, 1)] : List FactorBlock).map factorBlockValue).prod) = 758270641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_3159461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 758270641) ^ 379135320 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 758270641) ^ 252756880 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 758270641) ^ 151654128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 758270641) ^ 240 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_763380049 : Nat.Prime 763380049 := by
  apply lucas_primality 763380049 (7 : ZMod 763380049)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (283, 1), (56197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (283, 1), (56197, 1)] : List FactorBlock).map factorBlockValue).prod) = 763380049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_283
      · exact prime_ninetyEightCR_56197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 763380049) ^ 381690024 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 763380049) ^ 254460016 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 763380049) ^ 2697456 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 763380049) ^ 13584 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_779604977 : Nat.Prime 779604977 := by
  apply lucas_primality 779604977 (3 : ZMod 779604977)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (48725311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (48725311, 1)] : List FactorBlock).map factorBlockValue).prod) = 779604977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_48725311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 779604977) ^ 389802488 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 779604977) ^ 16 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_810768841 : Nat.Prime 810768841 := by
  apply lucas_primality 810768841 (37 : ZMod 810768841)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (965201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (965201, 1)] : List FactorBlock).map factorBlockValue).prod) = 810768841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_965201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 810768841) ^ 405384420 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (37 : ZMod 810768841) ^ 270256280 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (37 : ZMod 810768841) ^ 162153768 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (37 : ZMod 810768841) ^ 115824120 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (37 : ZMod 810768841) ^ 840 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_819178583 : Nat.Prime 819178583 := by
  apply lucas_primality 819178583 (5 : ZMod 819178583)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (6113273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (6113273, 1)] : List FactorBlock).map factorBlockValue).prod) = 819178583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_67
      · exact prime_ninetyEightCR_6113273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 819178583) ^ 409589291 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 819178583) ^ 12226546 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 819178583) ^ 134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_914216059 : Nat.Prime 914216059 := by
  apply lucas_primality 914216059 (2 : ZMod 914216059)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (268729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (268729, 1)] : List FactorBlock).map factorBlockValue).prod) = 914216059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_268729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 914216059) ^ 457108029 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 914216059) ^ 304738686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 914216059) ^ 130602294 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 914216059) ^ 3402 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_957335927 : Nat.Prime 957335927 := by
  apply lucas_primality 957335927 (7 : ZMod 957335927)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (53, 1), (531263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (53, 1), (531263, 1)] : List FactorBlock).map factorBlockValue).prod) = 957335927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_53
      · exact prime_ninetyEightCR_531263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 957335927) ^ 478667963 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 957335927) ^ 56313878 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 957335927) ^ 18062942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 957335927) ^ 1802 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1054733599 : Nat.Prime 1054733599 := by
  apply lucas_primality 1054733599 (15 : ZMod 1054733599)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (173, 1), (338707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (173, 1), (338707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1054733599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_173
      · exact prime_ninetyEightCR_338707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 1054733599) ^ 527366799 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 1054733599) ^ 351577866 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 1054733599) ^ 6096726 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 1054733599) ^ 3114 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1087175351 : Nat.Prime 1087175351 := by
  apply lucas_primality 1087175351 (11 : ZMod 1087175351)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (21743507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (21743507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1087175351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_21743507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1087175351) ^ 543587675 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1087175351) ^ 217435070 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 1087175351) ^ 50 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1095700003 : Nat.Prime 1095700003 := by
  apply lucas_primality 1095700003 (2 : ZMod 1095700003)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (3885461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (3885461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1095700003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_47
      · exact prime_ninetyEightCR_3885461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1095700003) ^ 547850001 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095700003) ^ 365233334 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095700003) ^ 23312766 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095700003) ^ 282 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1126846447 : Nat.Prime 1126846447 := by
  apply lucas_primality 1126846447 (5 : ZMod 1126846447)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (337, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (337, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126846447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_337
      · exact prime_ninetyEightCR_1747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1126846447) ^ 563423223 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126846447) ^ 375615482 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126846447) ^ 102440586 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126846447) ^ 38856774 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126846447) ^ 3343758 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126846447) ^ 645018 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1231259707 : Nat.Prime 1231259707 := by
  apply lucas_primality 1231259707 (3 : ZMod 1231259707)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (963427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (963427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1231259707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_71
      · exact prime_ninetyEightCR_963427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1231259707) ^ 615629853 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1231259707) ^ 410419902 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1231259707) ^ 17341686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1231259707) ^ 1278 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1271223221 : Nat.Prime 1271223221 := by
  apply lucas_primality 1271223221 (2 : ZMod 1271223221)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (63561161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (63561161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1271223221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_63561161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1271223221) ^ 635611610 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1271223221) ^ 254244644 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1271223221) ^ 20 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1305860447 : Nat.Prime 1305860447 := by
  apply lucas_primality 1305860447 (5 : ZMod 1305860447)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1361, 1), (43613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1361, 1), (43613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1305860447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_1361
      · exact prime_ninetyEightCR_43613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1305860447) ^ 652930223 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1305860447) ^ 118714586 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1305860447) ^ 959486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1305860447) ^ 29942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1453664689 : Nat.Prime 1453664689 := by
  apply lucas_primality 1453664689 (17 : ZMod 1453664689)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (4326383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (4326383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1453664689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_4326383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1453664689) ^ 726832344 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1453664689) ^ 484554896 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1453664689) ^ 207666384 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (17 : ZMod 1453664689) ^ 336 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1476219119 : Nat.Prime 1476219119 := by
  apply lucas_primality 1476219119 (7 : ZMod 1476219119)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (37, 1), (113, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (37, 1), (113, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1476219119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1476219119) ^ 738109559 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1476219119) ^ 134201738 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1476219119) ^ 39897814 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1476219119) ^ 13063886 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1476219119) ^ 1011802 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2027609581 : Nat.Prime 2027609581 := by
  apply lucas_primality 2027609581 (6 : ZMod 2027609581)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (571, 1), (59183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (571, 1), (59183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2027609581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_571
      · exact prime_ninetyEightCR_59183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2027609581) ^ 1013804790 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2027609581) ^ 675869860 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2027609581) ^ 405521916 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2027609581) ^ 3550980 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2027609581) ^ 34260 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2271588811 : Nat.Prime 2271588811 := by
  apply lucas_primality 2271588811 (2 : ZMod 2271588811)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (401, 1), (188827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (401, 1), (188827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2271588811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_401
      · exact prime_ninetyEightCR_188827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2271588811) ^ 1135794405 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271588811) ^ 757196270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271588811) ^ 454317762 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271588811) ^ 5664810 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2271588811) ^ 12030 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2368673683 : Nat.Prime 2368673683 := by
  apply lucas_primality 2368673683 (5 : ZMod 2368673683)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (113, 1), (205507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (113, 1), (205507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2368673683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_205507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2368673683) ^ 1184336841 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2368673683) ^ 789557894 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2368673683) ^ 139333746 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2368673683) ^ 20961714 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2368673683) ^ 11526 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2427205493 : Nat.Prime 2427205493 := by
  apply lucas_primality 2427205493 (2 : ZMod 2427205493)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9923, 1), (61151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9923, 1), (61151, 1)] : List FactorBlock).map factorBlockValue).prod) = 2427205493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_9923
      · exact prime_ninetyEightCR_61151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2427205493) ^ 1213602746 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2427205493) ^ 244604 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2427205493) ^ 39692 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2525024549 : Nat.Prime 2525024549 := by
  apply lucas_primality 2525024549 (3 : ZMod 2525024549)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (29, 1), (946411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (29, 1), (946411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2525024549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_946411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2525024549) ^ 1262512274 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2525024549) ^ 109783676 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2525024549) ^ 87069812 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2525024549) ^ 2668 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3021328469 : Nat.Prime 3021328469 := by
  apply lucas_primality 3021328469 (2 : ZMod 3021328469)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (823, 1), (53987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (823, 1), (53987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3021328469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_823
      · exact prime_ninetyEightCR_53987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3021328469) ^ 1510664234 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3021328469) ^ 177725204 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3021328469) ^ 3671116 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3021328469) ^ 55964 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3152949599 : Nat.Prime 3152949599 := by
  apply lucas_primality 3152949599 (7 : ZMod 3152949599)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (47, 1), (906541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (47, 1), (906541, 1)] : List FactorBlock).map factorBlockValue).prod) = 3152949599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_47
      · exact prime_ninetyEightCR_906541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3152949599) ^ 1576474799 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3152949599) ^ 85214854 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3152949599) ^ 67084034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3152949599) ^ 3478 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3188268529 : Nat.Prime 3188268529 := by
  apply lucas_primality 3188268529 (7 : ZMod 3188268529)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (733, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (733, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) = 3188268529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_733
      · exact prime_ninetyEightCR_90617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3188268529) ^ 1594134264 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3188268529) ^ 1062756176 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3188268529) ^ 4349616 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 3188268529) ^ 35184 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3689826299 : Nat.Prime 3689826299 := by
  apply lucas_primality 3689826299 (2 : ZMod 3689826299)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (23353331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (23353331, 1)] : List FactorBlock).map factorBlockValue).prod) = 3689826299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_79
      · exact prime_ninetyEightCR_23353331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3689826299) ^ 1844913149 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689826299) ^ 46706662 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3689826299) ^ 158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4127488247 : Nat.Prime 4127488247 := by
  apply lucas_primality 4127488247 (10 : ZMod 4127488247)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (42117227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (42117227, 1)] : List FactorBlock).map factorBlockValue).prod) = 4127488247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_42117227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4127488247) ^ 2063744123 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4127488247) ^ 589641178 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 4127488247) ^ 98 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4372724123 : Nat.Prime 4372724123 := by
  apply lucas_primality 4372724123 (2 : ZMod 4372724123)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (61, 1), (157, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (61, 1), (157, 1), (1033, 1)] : List FactorBlock).map factorBlockValue).prod) = 4372724123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_61
      · exact prime_ninetyEightCR_157
      · exact prime_ninetyEightCR_1033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4372724123) ^ 2186362061 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4372724123) ^ 336363394 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4372724123) ^ 257219066 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4372724123) ^ 71684002 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4372724123) ^ 27851746 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4372724123) ^ 4233034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4786097573 : Nat.Prime 4786097573 := by
  apply lucas_primality 4786097573 (2 : ZMod 4786097573)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (293, 1), (4083701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (293, 1), (4083701, 1)] : List FactorBlock).map factorBlockValue).prod) = 4786097573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_293
      · exact prime_ninetyEightCR_4083701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4786097573) ^ 2393048786 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4786097573) ^ 16334804 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 4786097573) ^ 1172 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4989491671 : Nat.Prime 4989491671 := by
  apply lucas_primality 4989491671 (15 : ZMod 4989491671)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (43, 1), (227519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (43, 1), (227519, 1)] : List FactorBlock).map factorBlockValue).prod) = 4989491671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_43
      · exact prime_ninetyEightCR_227519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 4989491671) ^ 2494745835 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 4989491671) ^ 1663163890 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 4989491671) ^ 997898334 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 4989491671) ^ 293499510 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 4989491671) ^ 116034690 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (15 : ZMod 4989491671) ^ 21930 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5084369989 : Nat.Prime 5084369989 := by
  apply lucas_primality 5084369989 (2 : ZMod 5084369989)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1997, 1), (212167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1997, 1), (212167, 1)] : List FactorBlock).map factorBlockValue).prod) = 5084369989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_1997
      · exact prime_ninetyEightCR_212167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5084369989) ^ 2542184994 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5084369989) ^ 1694789996 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5084369989) ^ 2546004 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5084369989) ^ 23964 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5234980739 : Nat.Prime 5234980739 := by
  apply lucas_primality 5234980739 (2 : ZMod 5234980739)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (10597127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (10597127, 1)] : List FactorBlock).map factorBlockValue).prod) = 5234980739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_10597127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5234980739) ^ 2617490369 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5234980739) ^ 402690826 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5234980739) ^ 275525302 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5234980739) ^ 494 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5305362347 : Nat.Prime 5305362347 := by
  apply lucas_primality 5305362347 (5 : ZMod 5305362347)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (156040069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (156040069, 1)] : List FactorBlock).map factorBlockValue).prod) = 5305362347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_156040069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5305362347) ^ 2652681173 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5305362347) ^ 312080138 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 5305362347) ^ 34 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5519454907 : Nat.Prime 5519454907 := by
  apply lucas_primality 5519454907 (3 : ZMod 5519454907)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (181, 1), (42709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (181, 1), (42709, 1)] : List FactorBlock).map factorBlockValue).prod) = 5519454907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_181
      · exact prime_ninetyEightCR_42709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5519454907) ^ 2759727453 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5519454907) ^ 1839818302 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5519454907) ^ 788493558 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5519454907) ^ 324673818 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5519454907) ^ 30494226 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 5519454907) ^ 129234 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5752573901 : Nat.Prime 5752573901 := by
  apply lucas_primality 5752573901 (2 : ZMod 5752573901)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 2), (31, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 2), (31, 1), (6421, 1)] : List FactorBlock).map factorBlockValue).prod) = 5752573901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_6421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5752573901) ^ 2876286950 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5752573901) ^ 1150514780 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5752573901) ^ 338386700 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5752573901) ^ 185566900 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5752573901) ^ 895900 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_6090923939 : Nat.Prime 6090923939 := by
  apply lucas_primality 6090923939 (2 : ZMod 6090923939)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (439, 1), (577, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (439, 1), (577, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 6090923939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_439
      · exact prime_ninetyEightCR_577
      · exact prime_ninetyEightCR_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6090923939) ^ 3045461969 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6090923939) ^ 553720358 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6090923939) ^ 13874542 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6090923939) ^ 10556194 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6090923939) ^ 5572666 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_6385161113 : Nat.Prime 6385161113 := by
  apply lucas_primality 6385161113 (3 : ZMod 6385161113)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (157, 1), (419, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (157, 1), (419, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 6385161113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_157
      · exact prime_ninetyEightCR_419
      · exact prime_ninetyEightCR_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6385161113) ^ 3192580556 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6385161113) ^ 580469192 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6385161113) ^ 40669816 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6385161113) ^ 15239048 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6385161113) ^ 5788904 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_7370801573 : Nat.Prime 7370801573 := by
  apply lucas_primality 7370801573 (2 : ZMod 7370801573)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (3463, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (3463, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) = 7370801573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_107
      · exact prime_ninetyEightCR_3463
      · exact prime_ninetyEightCR_4973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7370801573) ^ 3685400786 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370801573) ^ 68885996 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370801573) ^ 2128444 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370801573) ^ 1482164 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_7632276593 : Nat.Prime 7632276593 := by
  apply lucas_primality 7632276593 (3 : ZMod 7632276593)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (67, 1), (374719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (67, 1), (374719, 1)] : List FactorBlock).map factorBlockValue).prod) = 7632276593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_67
      · exact prime_ninetyEightCR_374719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7632276593) ^ 3816138296 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 7632276593) ^ 401698768 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 7632276593) ^ 113914576 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 7632276593) ^ 20368 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_7689202643 : Nat.Prime 7689202643 := by
  apply lucas_primality 7689202643 (5 : ZMod 7689202643)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1979, 1), (176609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1979, 1), (176609, 1)] : List FactorBlock).map factorBlockValue).prod) = 7689202643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_1979
      · exact prime_ninetyEightCR_176609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7689202643) ^ 3844601321 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7689202643) ^ 699018422 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7689202643) ^ 3885398 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 7689202643) ^ 43538 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8769488339 : Nat.Prime 8769488339 := by
  apply lucas_primality 8769488339 (2 : ZMod 8769488339)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (83, 1), (4063711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (83, 1), (4063711, 1)] : List FactorBlock).map factorBlockValue).prod) = 8769488339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_83
      · exact prime_ninetyEightCR_4063711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8769488339) ^ 4384744169 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8769488339) ^ 674576026 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8769488339) ^ 105656486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8769488339) ^ 2158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8957826043 : Nat.Prime 8957826043 := by
  apply lucas_primality 8957826043 (2 : ZMod 8957826043)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (41, 1), (3310357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (41, 1), (3310357, 1)] : List FactorBlock).map factorBlockValue).prod) = 8957826043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_41
      · exact prime_ninetyEightCR_3310357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8957826043) ^ 4478913021 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8957826043) ^ 2985942014 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8957826043) ^ 814347822 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8957826043) ^ 218483562 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8957826043) ^ 2706 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8991161887 : Nat.Prime 8991161887 := by
  apply lucas_primality 8991161887 (3 : ZMod 8991161887)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (191, 1), (48731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (191, 1), (48731, 1)] : List FactorBlock).map factorBlockValue).prod) = 8991161887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_191
      · exact prime_ninetyEightCR_48731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8991161887) ^ 4495580943 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8991161887) ^ 2997053962 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8991161887) ^ 1284451698 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8991161887) ^ 390920082 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8991161887) ^ 47074146 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8991161887) ^ 184506 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_9110949623 : Nat.Prime 9110949623 := by
  apply lucas_primality 9110949623 (5 : ZMod 9110949623)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (263, 1), (317, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (263, 1), (317, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 9110949623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_101
      · exact prime_ninetyEightCR_263
      · exact prime_ninetyEightCR_317
      · exact prime_ninetyEightCR_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9110949623) ^ 4555474811 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9110949623) ^ 90207422 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9110949623) ^ 34642394 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9110949623) ^ 28741166 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 9110949623) ^ 16840942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_10668402769 : Nat.Prime 10668402769 := by
  apply lucas_primality 10668402769 (11 : ZMod 10668402769)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (373, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (373, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) = 10668402769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_373
      · exact prime_ninetyEightCR_35051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10668402769) ^ 5334201384 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 10668402769) ^ 3556134256 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 10668402769) ^ 627553104 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 10668402769) ^ 28601616 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 10668402769) ^ 304368 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_10800053639 : Nat.Prime 10800053639 := by
  apply lucas_primality 10800053639 (7 : ZMod 10800053639)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (490911529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (490911529, 1)] : List FactorBlock).map factorBlockValue).prod) = 10800053639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_490911529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10800053639) ^ 5400026819 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 10800053639) ^ 981823058 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 10800053639) ^ 22 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_11505147803 : Nat.Prime 11505147803 := by
  apply lucas_primality 11505147803 (2 : ZMod 11505147803)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5752573901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5752573901, 1)] : List FactorBlock).map factorBlockValue).prod) = 11505147803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5752573901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11505147803) ^ 5752573901 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 11505147803) ^ 2 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_13864573297 : Nat.Prime 13864573297 := by
  apply lucas_primality 13864573297 (10 : ZMod 13864573297)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (19, 1), (723923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (19, 1), (723923, 1)] : List FactorBlock).map factorBlockValue).prod) = 13864573297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_723923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 13864573297) ^ 6932286648 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 13864573297) ^ 4621524432 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 13864573297) ^ 1980653328 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 13864573297) ^ 729714384 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 13864573297) ^ 19152 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_16509212459 : Nat.Prime 16509212459 := by
  apply lucas_primality 16509212459 (2 : ZMod 16509212459)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (13679, 1), (26237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (13679, 1), (26237, 1)] : List FactorBlock).map factorBlockValue).prod) = 16509212459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_13679
      · exact prime_ninetyEightCR_26237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16509212459) ^ 8254606229 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16509212459) ^ 717791846 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16509212459) ^ 1206902 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16509212459) ^ 629234 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_16601685197 : Nat.Prime 16601685197 := by
  apply lucas_primality 16601685197 (2 : ZMod 16601685197)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16993, 1), (244243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16993, 1), (244243, 1)] : List FactorBlock).map factorBlockValue).prod) = 16601685197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_16993
      · exact prime_ninetyEightCR_244243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16601685197) ^ 8300842598 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16601685197) ^ 976972 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 16601685197) ^ 67972 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_18507017693 : Nat.Prime 18507017693 := by
  apply lucas_primality 18507017693 (2 : ZMod 18507017693)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20149, 1), (229627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20149, 1), (229627, 1)] : List FactorBlock).map factorBlockValue).prod) = 18507017693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_20149
      · exact prime_ninetyEightCR_229627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18507017693) ^ 9253508846 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18507017693) ^ 918508 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18507017693) ^ 80596 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_22077819629 : Nat.Prime 22077819629 := by
  apply lucas_primality 22077819629 (2 : ZMod 22077819629)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5519454907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5519454907, 1)] : List FactorBlock).map factorBlockValue).prod) = 22077819629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5519454907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22077819629) ^ 11038909814 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 22077819629) ^ 4 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_26734852471 : Nat.Prime 26734852471 := by
  apply lucas_primality 26734852471 (13 : ZMod 26734852471)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (61, 1), (307, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (61, 1), (307, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) = 26734852471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_61
      · exact prime_ninetyEightCR_307
      · exact prime_ninetyEightCR_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 26734852471) ^ 13367426235 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 8911617490 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 5346970494 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 1162384890 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 438276270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 87084210 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 26734852471) ^ 12921630 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_30808138349 : Nat.Prime 30808138349 := by
  apply lucas_primality 30808138349 (2 : ZMod 30808138349)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (631, 1), (40823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (631, 1), (40823, 1)] : List FactorBlock).map factorBlockValue).prod) = 30808138349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_631
      · exact prime_ninetyEightCR_40823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30808138349) ^ 15404069174 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30808138349) ^ 2369856796 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30808138349) ^ 1339484276 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30808138349) ^ 48824308 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30808138349) ^ 754676 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_38259222349 : Nat.Prime 38259222349 := by
  apply lucas_primality 38259222349 (6 : ZMod 38259222349)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3188268529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3188268529, 1)] : List FactorBlock).map factorBlockValue).prod) = 38259222349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_3188268529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 38259222349) ^ 19129611174 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 38259222349) ^ 12753074116 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 38259222349) ^ 12 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_39973022503 : Nat.Prime 39973022503 := by
  apply lucas_primality 39973022503 (5 : ZMod 39973022503)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4649, 1), (204719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4649, 1), (204719, 1)] : List FactorBlock).map factorBlockValue).prod) = 39973022503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_4649
      · exact prime_ninetyEightCR_204719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39973022503) ^ 19986511251 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 39973022503) ^ 13324340834 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 39973022503) ^ 5710431786 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 39973022503) ^ 8598198 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 39973022503) ^ 195258 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_40171627877 : Nat.Prime 40171627877 := by
  apply lucas_primality 40171627877 (2 : ZMod 40171627877)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (293, 1), (1804007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (293, 1), (1804007, 1)] : List FactorBlock).map factorBlockValue).prod) = 40171627877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_293
      · exact prime_ninetyEightCR_1804007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40171627877) ^ 20085813938 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40171627877) ^ 2114296204 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40171627877) ^ 137104532 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40171627877) ^ 22268 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_40853784443 : Nat.Prime 40853784443 := by
  apply lucas_primality 40853784443 (2 : ZMod 40853784443)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (116437, 1), (175433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (116437, 1), (175433, 1)] : List FactorBlock).map factorBlockValue).prod) = 40853784443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_116437
      · exact prime_ninetyEightCR_175433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40853784443) ^ 20426892221 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40853784443) ^ 350866 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 40853784443) ^ 232874 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_41999318267 : Nat.Prime 41999318267 := by
  apply lucas_primality 41999318267 (2 : ZMod 41999318267)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (15649, 1), (46273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (15649, 1), (46273, 1)] : List FactorBlock).map factorBlockValue).prod) = 41999318267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_15649
      · exact prime_ninetyEightCR_46273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41999318267) ^ 20999659133 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41999318267) ^ 1448252354 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41999318267) ^ 2683834 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 41999318267) ^ 907642 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_42574786369 : Nat.Prime 42574786369 := by
  apply lucas_primality 42574786369 (7 : ZMod 42574786369)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (137, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (137, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) = 42574786369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_53
      · exact prime_ninetyEightCR_137
      · exact prime_ninetyEightCR_30539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42574786369) ^ 21287393184 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42574786369) ^ 14191595456 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42574786369) ^ 803297856 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42574786369) ^ 310764864 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 42574786369) ^ 1394112 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_45809131229 : Nat.Prime 45809131229 := by
  apply lucas_primality 45809131229 (2 : ZMod 45809131229)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1171, 1), (1397131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1171, 1), (1397131, 1)] : List FactorBlock).map factorBlockValue).prod) = 45809131229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_1171
      · exact prime_ninetyEightCR_1397131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45809131229) ^ 22904565614 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45809131229) ^ 6544161604 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45809131229) ^ 39119668 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45809131229) ^ 32788 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_70398841003 : Nat.Prime 70398841003 := by
  apply lucas_primality 70398841003 (2 : ZMod 70398841003)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (23, 1), (3835613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (23, 1), (3835613, 1)] : List FactorBlock).map factorBlockValue).prod) = 70398841003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_3835613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70398841003) ^ 35199420501 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 70398841003) ^ 23466280334 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 70398841003) ^ 10056977286 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 70398841003) ^ 3705202158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 70398841003) ^ 3060819174 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 70398841003) ^ 18354 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_73289730347 : Nat.Prime 73289730347 := by
  apply lucas_primality 73289730347 (2 : ZMod 73289730347)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5234980739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5234980739, 1)] : List FactorBlock).map factorBlockValue).prod) = 73289730347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_5234980739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 73289730347) ^ 36644865173 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 73289730347) ^ 10469961478 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 73289730347) ^ 14 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_73796525981 : Nat.Prime 73796525981 := by
  apply lucas_primality 73796525981 (2 : ZMod 73796525981)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3689826299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3689826299, 1)] : List FactorBlock).map factorBlockValue).prod) = 73796525981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_3689826299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 73796525981) ^ 36898262990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 73796525981) ^ 14759305196 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 73796525981) ^ 20 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_87442828471 : Nat.Prime 87442828471 := by
  apply lucas_primality 87442828471 (3 : ZMod 87442828471)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (51136157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (51136157, 1)] : List FactorBlock).map factorBlockValue).prod) = 87442828471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_51136157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87442828471) ^ 43721414235 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 87442828471) ^ 29147609490 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 87442828471) ^ 17488565694 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 87442828471) ^ 4602254130 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 87442828471) ^ 1710 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_93763352623 : Nat.Prime 93763352623 := by
  apply lucas_primality 93763352623 (3 : ZMod 93763352623)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (401, 1), (4861, 1), (8017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (401, 1), (4861, 1), (8017, 1)] : List FactorBlock).map factorBlockValue).prod) = 93763352623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_401
      · exact prime_ninetyEightCR_4861
      · exact prime_ninetyEightCR_8017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93763352623) ^ 46881676311 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 93763352623) ^ 31254450874 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 93763352623) ^ 233823822 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 93763352623) ^ 19288902 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 93763352623) ^ 11695566 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_97837148179 : Nat.Prime 97837148179 := by
  apply lucas_primality 97837148179 (3 : ZMod 97837148179)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (31, 1), (2277083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (31, 1), (2277083, 1)] : List FactorBlock).map factorBlockValue).prod) = 97837148179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_2277083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97837148179) ^ 48918574089 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 97837148179) ^ 32612382726 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 97837148179) ^ 13976735454 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 97837148179) ^ 8894286198 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 97837148179) ^ 3156037038 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 97837148179) ^ 42966 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_98411265919 : Nat.Prime 98411265919 := by
  apply lucas_primality 98411265919 (6 : ZMod 98411265919)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (111577399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (111577399, 1)] : List FactorBlock).map factorBlockValue).prod) = 98411265919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_111577399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 98411265919) ^ 49205632959 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 98411265919) ^ 32803755306 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 98411265919) ^ 14058752274 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 98411265919) ^ 882 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_100818259141 : Nat.Prime 100818259141 := by
  apply lucas_primality 100818259141 (7 : ZMod 100818259141)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3187, 1), (527237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3187, 1), (527237, 1)] : List FactorBlock).map factorBlockValue).prod) = 100818259141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_3187
      · exact prime_ninetyEightCR_527237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 100818259141) ^ 50409129570 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 100818259141) ^ 33606086380 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 100818259141) ^ 20163651828 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 100818259141) ^ 31634220 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 100818259141) ^ 191220 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_119106470929 : Nat.Prime 119106470929 := by
  apply lucas_primality 119106470929 (7 : ZMod 119106470929)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (313, 1), (7927747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (313, 1), (7927747, 1)] : List FactorBlock).map factorBlockValue).prod) = 119106470929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_313
      · exact prime_ninetyEightCR_7927747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119106470929) ^ 59553235464 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 119106470929) ^ 39702156976 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 119106470929) ^ 380531856 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 119106470929) ^ 15024 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_125875363667 : Nat.Prime 125875363667 := by
  apply lucas_primality 125875363667 (2 : ZMod 125875363667)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (71, 1), (383, 1), (178037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (71, 1), (383, 1), (178037, 1)] : List FactorBlock).map factorBlockValue).prod) = 125875363667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_71
      · exact prime_ninetyEightCR_383
      · exact prime_ninetyEightCR_178037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125875363667) ^ 62937681833 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 125875363667) ^ 9682720282 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 125875363667) ^ 1772892446 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 125875363667) ^ 328656302 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 125875363667) ^ 707018 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_136506715223 : Nat.Prime 136506715223 := by
  apply lucas_primality 136506715223 (5 : ZMod 136506715223)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6163, 1), (11074697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6163, 1), (11074697, 1)] : List FactorBlock).map factorBlockValue).prod) = 136506715223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_6163
      · exact prime_ninetyEightCR_11074697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 136506715223) ^ 68253357611 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 136506715223) ^ 22149394 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 136506715223) ^ 12326 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_165463059059 : Nat.Prime 165463059059 := by
  apply lucas_primality 165463059059 (2 : ZMod 165463059059)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (23, 1), (79, 1), (376297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (23, 1), (79, 1), (376297, 1)] : List FactorBlock).map factorBlockValue).prod) = 165463059059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_79
      · exact prime_ninetyEightCR_376297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 165463059059) ^ 82731529529 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 165463059059) ^ 15042096278 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 165463059059) ^ 7194046046 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 165463059059) ^ 2094469102 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 165463059059) ^ 439714 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_184282792891 : Nat.Prime 184282792891 := by
  apply lucas_primality 184282792891 (3 : ZMod 184282792891)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (263, 1), (3336643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (263, 1), (3336643, 1)] : List FactorBlock).map factorBlockValue).prod) = 184282792891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_263
      · exact prime_ninetyEightCR_3336643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 184282792891) ^ 92141396445 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 184282792891) ^ 61427597630 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 184282792891) ^ 36856558578 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 184282792891) ^ 26326113270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 184282792891) ^ 700695030 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 184282792891) ^ 55230 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_194323760791 : Nat.Prime 194323760791 := by
  apply lucas_primality 194323760791 (6 : ZMod 194323760791)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (373, 1), (209227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (373, 1), (209227, 1)] : List FactorBlock).map factorBlockValue).prod) = 194323760791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_83
      · exact prime_ninetyEightCR_373
      · exact prime_ninetyEightCR_209227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 194323760791) ^ 97161880395 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 194323760791) ^ 64774586930 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 194323760791) ^ 38864752158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 194323760791) ^ 2341250130 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 194323760791) ^ 520975230 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 194323760791) ^ 928770 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_213849353303 : Nat.Prime 213849353303 := by
  apply lucas_primality 213849353303 (5 : ZMod 213849353303)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (191, 1), (277, 1), (155461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (191, 1), (277, 1), (155461, 1)] : List FactorBlock).map factorBlockValue).prod) = 213849353303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_191
      · exact prime_ninetyEightCR_277
      · exact prime_ninetyEightCR_155461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 213849353303) ^ 106924676651 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 213849353303) ^ 16449950254 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 213849353303) ^ 1119630122 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 213849353303) ^ 772019326 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 213849353303) ^ 1375582 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_232485706883 : Nat.Prime 232485706883 := by
  apply lucas_primality 232485706883 (2 : ZMod 232485706883)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (101, 2), (79687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (101, 2), (79687, 1)] : List FactorBlock).map factorBlockValue).prod) = 232485706883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_101
      · exact prime_ninetyEightCR_79687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 232485706883) ^ 116242853441 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 232485706883) ^ 21135064262 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 232485706883) ^ 17883515914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 232485706883) ^ 2301838682 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 232485706883) ^ 2917486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_273013430447 : Nat.Prime 273013430447 := by
  apply lucas_primality 273013430447 (5 : ZMod 273013430447)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (136506715223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (136506715223, 1)] : List FactorBlock).map factorBlockValue).prod) = 273013430447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_136506715223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 273013430447) ^ 136506715223 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 273013430447) ^ 2 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_420475296523 : Nat.Prime 420475296523 := by
  apply lucas_primality 420475296523 (2 : ZMod 420475296523)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (991, 1), (70715657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (991, 1), (70715657, 1)] : List FactorBlock).map factorBlockValue).prod) = 420475296523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_991
      · exact prime_ninetyEightCR_70715657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 420475296523) ^ 210237648261 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 420475296523) ^ 140158432174 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 420475296523) ^ 424293942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 420475296523) ^ 5946 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_475319681411 : Nat.Prime 475319681411 := by
  apply lucas_primality 475319681411 (10 : ZMod 475319681411)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (251, 1), (4229, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (251, 1), (4229, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) = 475319681411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_251
      · exact prime_ninetyEightCR_4229
      · exact prime_ninetyEightCR_6397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 475319681411) ^ 237659840705 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 475319681411) ^ 95063936282 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 475319681411) ^ 67902811630 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 475319681411) ^ 1893703910 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 475319681411) ^ 112395290 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 475319681411) ^ 74303530 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_502089379117 : Nat.Prime 502089379117 := by
  apply lucas_primality 502089379117 (2 : ZMod 502089379117)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (71, 1), (45331291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (71, 1), (45331291, 1)] : List FactorBlock).map factorBlockValue).prod) = 502089379117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_71
      · exact prime_ninetyEightCR_45331291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 502089379117) ^ 251044689558 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 502089379117) ^ 167363126372 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 502089379117) ^ 38622259932 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 502089379117) ^ 7071681396 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 502089379117) ^ 11076 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_518476918033 : Nat.Prime 518476918033 := by
  apply lucas_primality 518476918033 (5 : ZMod 518476918033)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (31, 1), (101, 1), (383321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (31, 1), (101, 1), (383321, 1)] : List FactorBlock).map factorBlockValue).prod) = 518476918033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_101
      · exact prime_ninetyEightCR_383321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 518476918033) ^ 259238459016 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 518476918033) ^ 172825639344 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 518476918033) ^ 16725061872 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 518476918033) ^ 5133434832 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 518476918033) ^ 1352592 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_778189480637 : Nat.Prime 778189480637 := by
  apply lucas_primality 778189480637 (2 : ZMod 778189480637)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (23197, 1), (74219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (23197, 1), (74219, 1)] : List FactorBlock).map factorBlockValue).prod) = 778189480637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_23197
      · exact prime_ninetyEightCR_74219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 778189480637) ^ 389094740318 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 778189480637) ^ 6886632572 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 778189480637) ^ 33546988 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 778189480637) ^ 10485044 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1013016665293 : Nat.Prime 1013016665293 := by
  apply lucas_primality 1013016665293 (2 : ZMod 1013016665293)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (59, 1), (49338431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (59, 1), (49338431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013016665293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_59
      · exact prime_ninetyEightCR_49338431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1013016665293) ^ 506508332646 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013016665293) ^ 337672221764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013016665293) ^ 34931609148 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013016665293) ^ 17169773988 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1013016665293) ^ 20532 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1030738828237 : Nat.Prime 1030738828237 := by
  apply lucas_primality 1030738828237 (5 : ZMod 1030738828237)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (653, 1), (10118377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (653, 1), (10118377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1030738828237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_653
      · exact prime_ninetyEightCR_10118377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1030738828237) ^ 515369414118 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1030738828237) ^ 343579609412 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1030738828237) ^ 79287602172 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1030738828237) ^ 1578466812 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1030738828237) ^ 101868 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1037308780063 : Nat.Prime 1037308780063 := by
  apply lucas_primality 1037308780063 (3 : ZMod 1037308780063)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (5477, 1), (120941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (5477, 1), (120941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037308780063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_5477
      · exact prime_ninetyEightCR_120941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1037308780063) ^ 518654390031 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037308780063) ^ 345769593354 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037308780063) ^ 35769268278 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037308780063) ^ 189393606 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037308780063) ^ 8576982 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1162938892243 : Nat.Prime 1162938892243 := by
  apply lucas_primality 1162938892243 (2 : ZMod 1162938892243)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (47, 1), (217047199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (47, 1), (217047199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162938892243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_47
      · exact prime_ninetyEightCR_217047199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1162938892243) ^ 581469446121 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162938892243) ^ 387646297414 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162938892243) ^ 61207310118 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162938892243) ^ 24743380686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1162938892243) ^ 5358 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1235614985651 : Nat.Prime 1235614985651 := by
  apply lucas_primality 1235614985651 (2 : ZMod 1235614985651)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (1453664689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (1453664689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235614985651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_1453664689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1235614985651) ^ 617807492825 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235614985651) ^ 247122997130 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235614985651) ^ 72683234450 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235614985651) ^ 850 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1348510395173 : Nat.Prime 1348510395173 := by
  apply lucas_primality 1348510395173 (2 : ZMod 1348510395173)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (536671, 1), (628183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (536671, 1), (628183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348510395173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_536671
      · exact prime_ninetyEightCR_628183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1348510395173) ^ 674255197586 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348510395173) ^ 2512732 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348510395173) ^ 2146684 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1569801768259 : Nat.Prime 1569801768259 := by
  apply lucas_primality 1569801768259 (3 : ZMod 1569801768259)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (6857, 1), (1230829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (6857, 1), (1230829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569801768259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_6857
      · exact prime_ninetyEightCR_1230829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1569801768259) ^ 784900884129 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569801768259) ^ 523267256086 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569801768259) ^ 50638766718 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569801768259) ^ 228934194 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1569801768259) ^ 1275402 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1663838128177 : Nat.Prime 1663838128177 := by
  apply lucas_primality 1663838128177 (5 : ZMod 1663838128177)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (283, 1), (2777, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (283, 1), (2777, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1663838128177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_283
      · exact prime_ninetyEightCR_2777
      · exact prime_ninetyEightCR_6301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1663838128177) ^ 831919064088 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663838128177) ^ 554612709392 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663838128177) ^ 237691161168 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663838128177) ^ 5879286672 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663838128177) ^ 599149488 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663838128177) ^ 264059376 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1667842361197 : Nat.Prime 1667842361197 := by
  apply lucas_primality 1667842361197 (7 : ZMod 1667842361197)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (743245259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (743245259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667842361197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_743245259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1667842361197) ^ 833921180598 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1667842361197) ^ 555947453732 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1667842361197) ^ 151622032836 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1667842361197) ^ 98108374188 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1667842361197) ^ 2244 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1707175482541 : Nat.Prime 1707175482541 := by
  apply lucas_primality 1707175482541 (10 : ZMod 1707175482541)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (1409, 1), (79817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (23, 1), (1409, 1), (79817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1707175482541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_1409
      · exact prime_ninetyEightCR_79817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1707175482541) ^ 853587741270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 569058494180 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 341435096508 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 155197771140 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 74225020980 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 1211622060 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1707175482541) ^ 21388620 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1745435712707 : Nat.Prime 1745435712707 := by
  apply lucas_primality 1745435712707 (2 : ZMod 1745435712707)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (5051, 1), (3526147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (5051, 1), (3526147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1745435712707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_5051
      · exact prime_ninetyEightCR_3526147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1745435712707) ^ 872717856353 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1745435712707) ^ 249347958958 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1745435712707) ^ 345562406 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1745435712707) ^ 494998 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2135004331939 : Nat.Prime 2135004331939 := by
  apply lucas_primality 2135004331939 (2 : ZMod 2135004331939)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (1231259707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (1231259707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2135004331939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_1231259707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2135004331939) ^ 1067502165969 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2135004331939) ^ 711668110646 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2135004331939) ^ 125588490114 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2135004331939) ^ 1734 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2282745586103 : Nat.Prime 2282745586103 := by
  apply lucas_primality 2282745586103 (5 : ZMod 2282745586103)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (13063, 1), (3012913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (13063, 1), (3012913, 1)] : List FactorBlock).map factorBlockValue).prod) = 2282745586103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_13063
      · exact prime_ninetyEightCR_3012913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2282745586103) ^ 1141372793051 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2282745586103) ^ 78715365038 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2282745586103) ^ 174748954 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 2282745586103) ^ 757654 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2898876914831 : Nat.Prime 2898876914831 := by
  apply lucas_primality 2898876914831 (7 : ZMod 2898876914831)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (1993, 1), (2297, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (1993, 1), (2297, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2898876914831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_1993
      · exact prime_ninetyEightCR_2297
      · exact prime_ninetyEightCR_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2898876914831) ^ 1449438457415 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2898876914831) ^ 579775382966 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2898876914831) ^ 222990531910 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2898876914831) ^ 1454529310 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2898876914831) ^ 1262027390 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 2898876914831) ^ 595129730 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3246363453259 : Nat.Prime 3246363453259 := by
  apply lucas_primality 3246363453259 (2 : ZMod 3246363453259)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (19, 1), (31, 1), (443, 1), (13553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (19, 1), (31, 1), (443, 1), (13553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3246363453259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_443
      · exact prime_ninetyEightCR_13553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3246363453259) ^ 1623181726629 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 1082121151086 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 190962556074 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 170861234382 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 104721401718 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 7328134206 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3246363453259) ^ 239530986 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3840624996841 : Nat.Prime 3840624996841 := by
  apply lucas_primality 3840624996841 (11 : ZMod 3840624996841)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (10668402769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (10668402769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3840624996841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_10668402769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3840624996841) ^ 1920312498420 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 3840624996841) ^ 1280208332280 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 3840624996841) ^ 768124999368 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 3840624996841) ^ 360 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4391521008283 : Nat.Prime 4391521008283 := by
  apply lucas_primality 4391521008283 (3 : ZMod 4391521008283)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (2368673683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (2368673683, 1)] : List FactorBlock).map factorBlockValue).prod) = 4391521008283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_103
      · exact prime_ninetyEightCR_2368673683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4391521008283) ^ 2195760504141 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4391521008283) ^ 1463840336094 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4391521008283) ^ 42636126294 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4391521008283) ^ 1854 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5011831900133 : Nat.Prime 5011831900133 := by
  apply lucas_primality 5011831900133 (2 : ZMod 5011831900133)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (71, 1), (263392469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (71, 1), (263392469, 1)] : List FactorBlock).map factorBlockValue).prod) = 5011831900133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_67
      · exact prime_ninetyEightCR_71
      · exact prime_ninetyEightCR_263392469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5011831900133) ^ 2505915950066 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5011831900133) ^ 74803461196 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5011831900133) ^ 70589181692 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5011831900133) ^ 19028 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5307171041827 : Nat.Prime 5307171041827 := by
  apply lucas_primality 5307171041827 (2 : ZMod 5307171041827)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (29, 1), (5347, 1), (211271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (29, 1), (5347, 1), (211271, 1)] : List FactorBlock).map factorBlockValue).prod) = 5307171041827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_5347
      · exact prime_ninetyEightCR_211271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5307171041827) ^ 2653585520913 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5307171041827) ^ 1769057013942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5307171041827) ^ 183005897994 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5307171041827) ^ 992551158 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5307171041827) ^ 25120206 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5774730085171 : Nat.Prime 5774730085171 := by
  apply lucas_primality 5774730085171 (2 : ZMod 5774730085171)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (397, 1), (1429, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (397, 1), (1429, 1), (6653, 1)] : List FactorBlock).map factorBlockValue).prod) = 5774730085171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_397
      · exact prime_ninetyEightCR_1429
      · exact prime_ninetyEightCR_6653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5774730085171) ^ 2887365042585 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 1924910028390 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 1154946017034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 339690005010 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 14545919610 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 4041098730 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5774730085171) ^ 867988890 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_6074871250381 : Nat.Prime 6074871250381 := by
  apply lucas_primality 6074871250381 (2 : ZMod 6074871250381)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (131, 1), (2063, 1), (374641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (131, 1), (2063, 1), (374641, 1)] : List FactorBlock).map factorBlockValue).prod) = 6074871250381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_131
      · exact prime_ninetyEightCR_2063
      · exact prime_ninetyEightCR_374641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6074871250381) ^ 3037435625190 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6074871250381) ^ 2024957083460 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6074871250381) ^ 1214974250076 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6074871250381) ^ 46373062980 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6074871250381) ^ 2944678260 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 6074871250381) ^ 16215180 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_6223262995783 : Nat.Prime 6223262995783 := by
  apply lucas_primality 6223262995783 (3 : ZMod 6223262995783)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (5393, 1), (3052783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (5393, 1), (3052783, 1)] : List FactorBlock).map factorBlockValue).prod) = 6223262995783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_5393
      · exact prime_ninetyEightCR_3052783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6223262995783) ^ 3111631497891 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6223262995783) ^ 2074420998594 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6223262995783) ^ 889037570826 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6223262995783) ^ 1153951974 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 6223262995783) ^ 2038554 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_6666132647401 : Nat.Prime 6666132647401 := by
  apply lucas_primality 6666132647401 (26 : ZMod 6666132647401)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (251, 1), (44263829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (251, 1), (44263829, 1)] : List FactorBlock).map factorBlockValue).prod) = 6666132647401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_251
      · exact prime_ninetyEightCR_44263829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 6666132647401) ^ 3333066323700 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 6666132647401) ^ 2222044215800 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 6666132647401) ^ 1333226529480 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 6666132647401) ^ 26558297400 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (26 : ZMod 6666132647401) ^ 150600 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_9884919885209 : Nat.Prime 9884919885209 := by
  apply lucas_primality 9884919885209 (3 : ZMod 9884919885209)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1235614985651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1235614985651, 1)] : List FactorBlock).map factorBlockValue).prod) = 9884919885209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_1235614985651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 9884919885209) ^ 4942459942604 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 9884919885209) ^ 8 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_10228687885001 : Nat.Prime 10228687885001 := by
  apply lucas_primality 10228687885001 (3 : ZMod 10228687885001)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 4), (13, 1), (157364429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 4), (13, 1), (157364429, 1)] : List FactorBlock).map factorBlockValue).prod) = 10228687885001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_157364429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10228687885001) ^ 5114343942500 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10228687885001) ^ 2045737577000 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10228687885001) ^ 786822145000 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10228687885001) ^ 65000 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_18537224560181 : Nat.Prime 18537224560181 := by
  apply lucas_primality 18537224560181 (2 : ZMod 18537224560181)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (487, 1), (919, 1), (2070953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (487, 1), (919, 1), (2070953, 1)] : List FactorBlock).map factorBlockValue).prod) = 18537224560181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_487
      · exact prime_ninetyEightCR_919
      · exact prime_ninetyEightCR_2070953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18537224560181) ^ 9268612280090 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18537224560181) ^ 3707444912036 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18537224560181) ^ 38064116140 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18537224560181) ^ 20171082220 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18537224560181) ^ 8951060 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_18553298908267 : Nat.Prime 18553298908267 := by
  apply lucas_primality 18553298908267 (2 : ZMod 18553298908267)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1030738828237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1030738828237, 1)] : List FactorBlock).map factorBlockValue).prod) = 18553298908267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_1030738828237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18553298908267) ^ 9276649454133 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18553298908267) ^ 6184432969422 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 18553298908267) ^ 18 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_20295080724493 : Nat.Prime 20295080724493 := by
  apply lucas_primality 20295080724493 (5 : ZMod 20295080724493)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (11505147803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (11505147803, 1)] : List FactorBlock).map factorBlockValue).prod) = 20295080724493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11505147803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20295080724493) ^ 10147540362246 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20295080724493) ^ 6765026908164 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20295080724493) ^ 2899297246356 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 20295080724493) ^ 1764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_22286366636447 : Nat.Prime 22286366636447 := by
  apply lucas_primality 22286366636447 (5 : ZMod 22286366636447)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1013016665293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1013016665293, 1)] : List FactorBlock).map factorBlockValue).prod) = 22286366636447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_1013016665293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 22286366636447) ^ 11143183318223 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 22286366636447) ^ 2026033330586 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 22286366636447) ^ 22 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_33151217064041 : Nat.Prime 33151217064041 := by
  apply lucas_primality 33151217064041 (3 : ZMod 33151217064041)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (26734852471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (26734852471, 1)] : List FactorBlock).map factorBlockValue).prod) = 33151217064041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_31
      · exact prime_ninetyEightCR_26734852471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33151217064041) ^ 16575608532020 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 33151217064041) ^ 6630243412808 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 33151217064041) ^ 1069394098840 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 33151217064041) ^ 1240 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_38590987398217 : Nat.Prime 38590987398217 := by
  apply lucas_primality 38590987398217 (5 : ZMod 38590987398217)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (33247, 1), (258631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (33247, 1), (258631, 1)] : List FactorBlock).map factorBlockValue).prod) = 38590987398217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_33247
      · exact prime_ninetyEightCR_258631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38590987398217) ^ 19295493699108 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 38590987398217) ^ 12863662466072 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 38590987398217) ^ 3508271581656 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 38590987398217) ^ 2270058082248 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 38590987398217) ^ 1160735928 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 38590987398217) ^ 149212536 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_43954449511253 : Nat.Prime 43954449511253 := by
  apply lucas_primality 43954449511253 (2 : ZMod 43954449511253)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1569801768259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1569801768259, 1)] : List FactorBlock).map factorBlockValue).prod) = 43954449511253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_1569801768259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43954449511253) ^ 21977224755626 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43954449511253) ^ 6279207073036 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 43954449511253) ^ 28 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_50168444249449 : Nat.Prime 50168444249449 := by
  apply lucas_primality 50168444249449 (19 : ZMod 50168444249449)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (176537, 1), (563851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (176537, 1), (563851, 1)] : List FactorBlock).map factorBlockValue).prod) = 50168444249449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_176537
      · exact prime_ninetyEightCR_563851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 50168444249449) ^ 25084222124724 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 50168444249449) ^ 16722814749816 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 50168444249449) ^ 7166920607064 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 50168444249449) ^ 284180904 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (19 : ZMod 50168444249449) ^ 88974648 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_53071710418271 : Nat.Prime 53071710418271 := by
  apply lucas_primality 53071710418271 (34 : ZMod 53071710418271)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5307171041827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5307171041827, 1)] : List FactorBlock).map factorBlockValue).prod) = 53071710418271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_5307171041827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (34 : ZMod 53071710418271) ^ 26535855209135 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (34 : ZMod 53071710418271) ^ 10614342083654 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (34 : ZMod 53071710418271) ^ 10 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_54756669793289 : Nat.Prime 54756669793289 := by
  apply lucas_primality 54756669793289 (3 : ZMod 54756669793289)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10771, 1), (635464091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10771, 1), (635464091, 1)] : List FactorBlock).map factorBlockValue).prod) = 54756669793289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_10771
      · exact prime_ninetyEightCR_635464091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54756669793289) ^ 27378334896644 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54756669793289) ^ 5083712728 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 54756669793289) ^ 86168 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_132188702701469 : Nat.Prime 132188702701469 := by
  apply lucas_primality 132188702701469 (2 : ZMod 132188702701469)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (21193, 1), (222763417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (21193, 1), (222763417, 1)] : List FactorBlock).map factorBlockValue).prod) = 132188702701469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_21193
      · exact prime_ninetyEightCR_222763417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 132188702701469) ^ 66094351350734 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 132188702701469) ^ 18884100385924 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 132188702701469) ^ 6237375676 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 132188702701469) ^ 593404 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_138564688188371 : Nat.Prime 138564688188371 := by
  apply lucas_primality 138564688188371 (2 : ZMod 138564688188371)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1283, 1), (10800053639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1283, 1), (10800053639, 1)] : List FactorBlock).map factorBlockValue).prod) = 138564688188371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_1283
      · exact prime_ninetyEightCR_10800053639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 138564688188371) ^ 69282344094185 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 138564688188371) ^ 27712937637674 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 138564688188371) ^ 108000536390 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 138564688188371) ^ 12830 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_149204175234217 : Nat.Prime 149204175234217 := by
  apply lucas_primality 149204175234217 (5 : ZMod 149204175234217)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (1321, 1), (5179, 1), (53453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (1321, 1), (5179, 1), (53453, 1)] : List FactorBlock).map factorBlockValue).prod) = 149204175234217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_1321
      · exact prime_ninetyEightCR_5179
      · exact prime_ninetyEightCR_53453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 149204175234217) ^ 74602087617108 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 149204175234217) ^ 49734725078072 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 149204175234217) ^ 8776716190248 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 149204175234217) ^ 112947899496 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 149204175234217) ^ 28809456504 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 149204175234217) ^ 2791315272 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_154363949592869 : Nat.Prime 154363949592869 := by
  apply lucas_primality 154363949592869 (2 : ZMod 154363949592869)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (38590987398217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (38590987398217, 1)] : List FactorBlock).map factorBlockValue).prod) = 154363949592869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_38590987398217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 154363949592869) ^ 77181974796434 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 154363949592869) ^ 4 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_253779613919749 : Nat.Prime 253779613919749 := by
  apply lucas_primality 253779613919749 (2 : ZMod 253779613919749)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (61, 1), (16509212459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (61, 1), (16509212459, 1)] : List FactorBlock).map factorBlockValue).prod) = 253779613919749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_61
      · exact prime_ninetyEightCR_16509212459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 253779613919749) ^ 126889806959874 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 253779613919749) ^ 84593204639916 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 253779613919749) ^ 36254230559964 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 253779613919749) ^ 4160321539668 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 253779613919749) ^ 15372 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_256697725815757 : Nat.Prime 256697725815757 := by
  apply lucas_primality 256697725815757 (2 : ZMod 256697725815757)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (109, 1), (2267, 1), (5101, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (109, 1), (2267, 1), (5101, 1), (5657, 1)] : List FactorBlock).map factorBlockValue).prod) = 256697725815757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_109
      · exact prime_ninetyEightCR_2267
      · exact prime_ninetyEightCR_5101
      · exact prime_ninetyEightCR_5657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256697725815757) ^ 128348862907878 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 256697725815757) ^ 85565908605252 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 256697725815757) ^ 2355025007484 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 256697725815757) ^ 113232344868 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 256697725815757) ^ 50323020156 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 256697725815757) ^ 45377006508 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_288672252320107 : Nat.Prime 288672252320107 := by
  apply lucas_primality 288672252320107 (2 : ZMod 288672252320107)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (40823, 1), (392850779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (40823, 1), (392850779, 1)] : List FactorBlock).map factorBlockValue).prod) = 288672252320107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_40823
      · exact prime_ninetyEightCR_392850779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 288672252320107) ^ 144336126160053 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 288672252320107) ^ 96224084106702 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 288672252320107) ^ 7071314022 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 288672252320107) ^ 734814 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_290169869888089 : Nat.Prime 290169869888089 := by
  apply lucas_primality 290169869888089 (53 : ZMod 290169869888089)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3821, 1), (1054733599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3821, 1), (1054733599, 1)] : List FactorBlock).map factorBlockValue).prod) = 290169869888089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_3821
      · exact prime_ninetyEightCR_1054733599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (53 : ZMod 290169869888089) ^ 145084934944044 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (53 : ZMod 290169869888089) ^ 96723289962696 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (53 : ZMod 290169869888089) ^ 75940819128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (53 : ZMod 290169869888089) ^ 275112 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_382639201583371 : Nat.Prime 382639201583371 := by
  apply lucas_primality 382639201583371 (2 : ZMod 382639201583371)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (97001, 1), (1301879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (97001, 1), (1301879, 1)] : List FactorBlock).map factorBlockValue).prod) = 382639201583371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_101
      · exact prime_ninetyEightCR_97001
      · exact prime_ninetyEightCR_1301879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 382639201583371) ^ 191319600791685 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 382639201583371) ^ 127546400527790 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 382639201583371) ^ 76527840316674 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 382639201583371) ^ 3788506946370 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 382639201583371) ^ 3944693370 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 382639201583371) ^ 293913030 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_467041060583431 : Nat.Prime 467041060583431 := by
  apply lucas_primality 467041060583431 (3 : ZMod 467041060583431)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (279557, 1), (55688233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (279557, 1), (55688233, 1)] : List FactorBlock).map factorBlockValue).prod) = 467041060583431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_279557
      · exact prime_ninetyEightCR_55688233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 467041060583431) ^ 233520530291715 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 467041060583431) ^ 155680353527810 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 467041060583431) ^ 93408212116686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 467041060583431) ^ 1670646990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 467041060583431) ^ 8386710 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_656123910914189 : Nat.Prime 656123910914189 := by
  apply lucas_primality 656123910914189 (2 : ZMod 656123910914189)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (839, 1), (19949, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (839, 1), (19949, 1), (86729, 1)] : List FactorBlock).map factorBlockValue).prod) = 656123910914189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_839
      · exact prime_ninetyEightCR_19949
      · exact prime_ninetyEightCR_86729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 656123910914189) ^ 328061955457094 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 656123910914189) ^ 5806406291276 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 656123910914189) ^ 782030883092 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 656123910914189) ^ 32890065212 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 656123910914189) ^ 7565219372 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_822269212534811 : Nat.Prime 822269212534811 := by
  apply lucas_primality 822269212534811 (2 : ZMod 822269212534811)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (157, 1), (30808138349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (157, 1), (30808138349, 1)] : List FactorBlock).map factorBlockValue).prod) = 822269212534811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_157
      · exact prime_ninetyEightCR_30808138349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 822269212534811) ^ 411134606267405 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 822269212534811) ^ 164453842506962 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 822269212534811) ^ 48368777207930 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 822269212534811) ^ 5237383519330 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 822269212534811) ^ 26690 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_911303319187351 : Nat.Prime 911303319187351 := by
  apply lucas_primality 911303319187351 (3 : ZMod 911303319187351)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (223, 1), (13249, 1), (685429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (223, 1), (13249, 1), (685429, 1)] : List FactorBlock).map factorBlockValue).prod) = 911303319187351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_223
      · exact prime_ninetyEightCR_13249
      · exact prime_ninetyEightCR_685429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 911303319187351) ^ 455651659593675 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 911303319187351) ^ 303767773062450 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 911303319187351) ^ 182260663837470 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 911303319187351) ^ 4086561969450 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 911303319187351) ^ 68782800150 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 911303319187351) ^ 1329537150 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1015118455678997 : Nat.Prime 1015118455678997 := by
  apply lucas_primality 1015118455678997 (2 : ZMod 1015118455678997)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (253779613919749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (253779613919749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015118455678997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_253779613919749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1015118455678997) ^ 507559227839498 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1015118455678997) ^ 4 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1141775745708161 : Nat.Prime 1141775745708161 := by
  apply lucas_primality 1141775745708161 (3 : ZMod 1141775745708161)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (149, 1), (881, 1), (13590601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (149, 1), (881, 1), (13590601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141775745708161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_149
      · exact prime_ninetyEightCR_881
      · exact prime_ninetyEightCR_13590601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1141775745708161) ^ 570887872854080 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141775745708161) ^ 228355149141632 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141775745708161) ^ 7662924467840 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141775745708161) ^ 1295999711360 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1141775745708161) ^ 84012160 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1192371834135577 : Nat.Prime 1192371834135577 := by
  apply lucas_primality 1192371834135577 (5 : ZMod 1192371834135577)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (850043, 1), (1579639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (850043, 1), (1579639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1192371834135577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_850043
      · exact prime_ninetyEightCR_1579639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1192371834135577) ^ 596185917067788 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1192371834135577) ^ 397457278045192 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1192371834135577) ^ 32226265787448 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1192371834135577) ^ 1402719432 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1192371834135577) ^ 754838184 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1307277727938113 : Nat.Prime 1307277727938113 := by
  apply lucas_primality 1307277727938113 (3 : ZMod 1307277727938113)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (73, 1), (39973022503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (73, 1), (39973022503, 1)] : List FactorBlock).map factorBlockValue).prod) = 1307277727938113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_73
      · exact prime_ninetyEightCR_39973022503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1307277727938113) ^ 653638863969056 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307277727938113) ^ 186753961134016 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307277727938113) ^ 17907914081344 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1307277727938113) ^ 32704 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1540186354894543 : Nat.Prime 1540186354894543 := by
  apply lucas_primality 1540186354894543 (5 : ZMod 1540186354894543)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (256697725815757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (256697725815757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1540186354894543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_256697725815757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1540186354894543) ^ 770093177447271 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1540186354894543) ^ 513395451631514 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1540186354894543) ^ 6 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1569827154108769 : Nat.Prime 1569827154108769 := by
  apply lucas_primality 1569827154108769 (7 : ZMod 1569827154108769)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (191, 1), (1153, 1), (4367863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (191, 1), (1153, 1), (4367863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1569827154108769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_191
      · exact prime_ninetyEightCR_1153
      · exact prime_ninetyEightCR_4367863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1569827154108769) ^ 784913577054384 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1569827154108769) ^ 523275718036256 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1569827154108769) ^ 92342773771104 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1569827154108769) ^ 8218990335648 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1569827154108769) ^ 1361515311456 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1569827154108769) ^ 359403936 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2104217370164597 : Nat.Prime 2104217370164597 := by
  apply lucas_primality 2104217370164597 (2 : ZMod 2104217370164597)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109913, 1), (4786097573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109913, 1), (4786097573, 1)] : List FactorBlock).map factorBlockValue).prod) = 2104217370164597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_109913
      · exact prime_ninetyEightCR_4786097573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2104217370164597) ^ 1052108685082298 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2104217370164597) ^ 19144390292 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2104217370164597) ^ 439652 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2576594710116491 : Nat.Prime 2576594710116491 := by
  apply lucas_primality 2576594710116491 (6 : ZMod 2576594710116491)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (33857, 1), (1087175351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (33857, 1), (1087175351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2576594710116491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_33857
      · exact prime_ninetyEightCR_1087175351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2576594710116491) ^ 1288297355058245 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2576594710116491) ^ 515318942023298 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2576594710116491) ^ 368084958588070 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2576594710116491) ^ 76102274570 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 2576594710116491) ^ 2369990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2690909012712749 : Nat.Prime 2690909012712749 := by
  apply lucas_primality 2690909012712749 (2 : ZMod 2690909012712749)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (991927, 1), (23386289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (991927, 1), (23386289, 1)] : List FactorBlock).map factorBlockValue).prod) = 2690909012712749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_991927
      · exact prime_ninetyEightCR_23386289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2690909012712749) ^ 1345454506356374 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690909012712749) ^ 92789965955612 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690909012712749) ^ 2712809524 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2690909012712749) ^ 115063532 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2852654929465217 : Nat.Prime 2852654929465217 := by
  apply lucas_primality 2852654929465217 (3 : ZMod 2852654929465217)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (22286366636447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (22286366636447, 1)] : List FactorBlock).map factorBlockValue).prod) = 2852654929465217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_22286366636447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2852654929465217) ^ 1426327464732608 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 2852654929465217) ^ 128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8638922648436137 : Nat.Prime 8638922648436137 := by
  apply lucas_primality 8638922648436137 (3 : ZMod 8638922648436137)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (59, 1), (8467, 1), (308809027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (59, 1), (8467, 1), (308809027, 1)] : List FactorBlock).map factorBlockValue).prod) = 8638922648436137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_59
      · exact prime_ninetyEightCR_8467
      · exact prime_ninetyEightCR_308809027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8638922648436137) ^ 4319461324218068 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8638922648436137) ^ 1234131806919448 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8638922648436137) ^ 146422417770104 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8638922648436137) ^ 1020305025208 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8638922648436137) ^ 27974968 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_10676283616059631 : Nat.Prime 10676283616059631 := by
  apply lucas_primality 10676283616059631 (3 : ZMod 10676283616059631)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12239, 1), (90031, 1), (322969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12239, 1), (90031, 1), (322969, 1)] : List FactorBlock).map factorBlockValue).prod) = 10676283616059631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_12239
      · exact prime_ninetyEightCR_90031
      · exact prime_ninetyEightCR_322969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10676283616059631) ^ 5338141808029815 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10676283616059631) ^ 3558761205353210 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10676283616059631) ^ 2135256723211926 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10676283616059631) ^ 872316661170 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10676283616059631) ^ 118584527730 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 10676283616059631) ^ 33056682270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_14527432641899557 : Nat.Prime 14527432641899557 := by
  apply lucas_primality 14527432641899557 (2 : ZMod 14527432641899557)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (347, 1), (1162938892243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (347, 1), (1162938892243, 1)] : List FactorBlock).map factorBlockValue).prod) = 14527432641899557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_347
      · exact prime_ninetyEightCR_1162938892243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14527432641899557) ^ 7263716320949778 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14527432641899557) ^ 4842477547299852 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14527432641899557) ^ 41865800120748 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 14527432641899557) ^ 12492 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_20612757680931929 : Nat.Prime 20612757680931929 := by
  apply lucas_primality 20612757680931929 (3 : ZMod 20612757680931929)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2576594710116491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2576594710116491, 1)] : List FactorBlock).map factorBlockValue).prod) = 20612757680931929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_2576594710116491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20612757680931929) ^ 10306378840465964 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 20612757680931929) ^ 8 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_36937453561749229 : Nat.Prime 36937453561749229 := by
  apply lucas_primality 36937453561749229 (2 : ZMod 36937453561749229)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (193, 1), (2963, 1), (5693, 1), (32603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (193, 1), (2963, 1), (5693, 1), (32603, 1)] : List FactorBlock).map factorBlockValue).prod) = 36937453561749229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_193
      · exact prime_ninetyEightCR_2963
      · exact prime_ninetyEightCR_5693
      · exact prime_ninetyEightCR_32603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36937453561749229) ^ 18468726780874614 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 12312484520583076 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 1273705295232732 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 191385769749996 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 12466234749156 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 6488223003996 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 36937453561749229) ^ 1132946463876 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_49272680258707403 : Nat.Prime 49272680258707403 := by
  apply lucas_primality 49272680258707403 (2 : ZMod 49272680258707403)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (86813, 1), (1095700003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (86813, 1), (1095700003, 1)] : List FactorBlock).map factorBlockValue).prod) = 49272680258707403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_37
      · exact prime_ninetyEightCR_86813
      · exact prime_ninetyEightCR_1095700003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49272680258707403) ^ 24636340129353701 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 49272680258707403) ^ 7038954322672486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 49272680258707403) ^ 1331694061046146 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 49272680258707403) ^ 567572601554 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 49272680258707403) ^ 44969134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_50305175479592069 : Nat.Prime 50305175479592069 := by
  apply lucas_primality 50305175479592069 (2 : ZMod 50305175479592069)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (2221, 1), (42574786369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (2221, 1), (42574786369, 1)] : List FactorBlock).map factorBlockValue).prod) = 50305175479592069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_2221
      · exact prime_ninetyEightCR_42574786369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50305175479592069) ^ 25152587739796034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50305175479592069) ^ 7186453639941724 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50305175479592069) ^ 2647640814715372 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50305175479592069) ^ 22649786348308 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 50305175479592069) ^ 1181572 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_69759997316650187 : Nat.Prime 69759997316650187 := by
  apply lucas_primality 69759997316650187 (2 : ZMod 69759997316650187)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (54756669793289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (54756669793289, 1)] : List FactorBlock).map factorBlockValue).prod) = 69759997316650187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_54756669793289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69759997316650187) ^ 34879998658325093 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 69759997316650187) ^ 9965713902378598 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 69759997316650187) ^ 5366153639742322 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 69759997316650187) ^ 1274 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_84215967930088013 : Nat.Prime 84215967930088013 := by
  apply lucas_primality 84215967930088013 (2 : ZMod 84215967930088013)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (941, 1), (3399041, 1), (6582463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (941, 1), (3399041, 1), (6582463, 1)] : List FactorBlock).map factorBlockValue).prod) = 84215967930088013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_941
      · exact prime_ninetyEightCR_3399041
      · exact prime_ninetyEightCR_6582463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84215967930088013) ^ 42107983965044006 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84215967930088013) ^ 89496246471932 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84215967930088013) ^ 24776390732 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 84215967930088013) ^ 12793990324 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_91813132273080749 : Nat.Prime 91813132273080749 := by
  apply lucas_primality 91813132273080749 (2 : ZMod 91813132273080749)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (107, 1), (2897, 1), (763380049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (107, 1), (2897, 1), (763380049, 1)] : List FactorBlock).map factorBlockValue).prod) = 91813132273080749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_97
      · exact prime_ninetyEightCR_107
      · exact prime_ninetyEightCR_2897
      · exact prime_ninetyEightCR_763380049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91813132273080749) ^ 45906566136540374 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 91813132273080749) ^ 946527136835884 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 91813132273080749) ^ 858066656757764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 91813132273080749) ^ 31692486114284 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 91813132273080749) ^ 120271852 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_98518017202897771 : Nat.Prime 98518017202897771 := by
  apply lucas_primality 98518017202897771 (10 : ZMod 98518017202897771)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (18553298908267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (18553298908267, 1)] : List FactorBlock).map factorBlockValue).prod) = 98518017202897771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_59
      · exact prime_ninetyEightCR_18553298908267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 98518017202897771) ^ 49259008601448885 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 98518017202897771) ^ 32839339067632590 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 98518017202897771) ^ 19703603440579554 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 98518017202897771) ^ 1669796901744030 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 98518017202897771) ^ 5310 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_99384626579637391 : Nat.Prime 99384626579637391 := by
  apply lucas_primality 99384626579637391 (13 : ZMod 99384626579637391)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (661, 1), (5011831900133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (661, 1), (5011831900133, 1)] : List FactorBlock).map factorBlockValue).prod) = 99384626579637391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_661
      · exact prime_ninetyEightCR_5011831900133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 99384626579637391) ^ 49692313289818695 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 99384626579637391) ^ 33128208859879130 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 99384626579637391) ^ 19876925315927478 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 99384626579637391) ^ 150354957003990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (13 : ZMod 99384626579637391) ^ 19830 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_105556148725735541 : Nat.Prime 105556148725735541 := by
  apply lucas_primality 105556148725735541 (2 : ZMod 105556148725735541)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (109, 1), (151, 1), (45809131229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (109, 1), (151, 1), (45809131229, 1)] : List FactorBlock).map factorBlockValue).prod) = 105556148725735541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_109
      · exact prime_ninetyEightCR_151
      · exact prime_ninetyEightCR_45809131229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105556148725735541) ^ 52778074362867770 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105556148725735541) ^ 21111229745147108 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105556148725735541) ^ 15079449817962220 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105556148725735541) ^ 968405034181060 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105556148725735541) ^ 699047342554540 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 105556148725735541) ^ 2304260 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_143643907672236887 : Nat.Prime 143643907672236887 := by
  apply lucas_primality 143643907672236887 (5 : ZMod 143643907672236887)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (73, 1), (7573, 1), (3021328469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (73, 1), (7573, 1), (3021328469, 1)] : List FactorBlock).map factorBlockValue).prod) = 143643907672236887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_43
      · exact prime_ninetyEightCR_73
      · exact prime_ninetyEightCR_7573
      · exact prime_ninetyEightCR_3021328469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 143643907672236887) ^ 71821953836118443 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 143643907672236887) ^ 3340555992377602 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 143643907672236887) ^ 1967724762633382 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 143643907672236887) ^ 18967900128382 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 143643907672236887) ^ 47543294 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_154460873306134049 : Nat.Prime 154460873306134049 := by
  apply lucas_primality 154460873306134049 (3 : ZMod 154460873306134049)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (120157, 1), (40171627877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (120157, 1), (40171627877, 1)] : List FactorBlock).map factorBlockValue).prod) = 154460873306134049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_120157
      · exact prime_ninetyEightCR_40171627877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 154460873306134049) ^ 77230436653067024 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 154460873306134049) ^ 1285492092064 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 154460873306134049) ^ 3845024 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_162792910026797821 : Nat.Prime 162792910026797821 := by
  apply lucas_primality 162792910026797821 (18 : ZMod 162792910026797821)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (59, 1), (50873, 1), (1677089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (59, 1), (50873, 1), (1677089, 1)] : List FactorBlock).map factorBlockValue).prod) = 162792910026797821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_59
      · exact prime_ninetyEightCR_50873
      · exact prime_ninetyEightCR_1677089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 162792910026797821) ^ 81396455013398910 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 54264303342265940 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 32558582005359564 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 23256130003828260 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 14799355456981620 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 2759201864860980 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 3199986437340 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (18 : ZMod 162792910026797821) ^ 97068736380 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_198744188856879257 : Nat.Prime 198744188856879257 := by
  apply lucas_primality 198744188856879257 (3 : ZMod 198744188856879257)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (131841631, 1), (188430797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (131841631, 1), (188430797, 1)] : List FactorBlock).map factorBlockValue).prod) = 198744188856879257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_131841631
      · exact prime_ninetyEightCR_188430797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 198744188856879257) ^ 99372094428439628 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 198744188856879257) ^ 1507446376 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 198744188856879257) ^ 1054733048 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_206022908027055347 : Nat.Prime 206022908027055347 := by
  apply lucas_primality 206022908027055347 (2 : ZMod 206022908027055347)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (656123910914189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (656123910914189, 1)] : List FactorBlock).map factorBlockValue).prod) = 206022908027055347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_157
      · exact prime_ninetyEightCR_656123910914189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 206022908027055347) ^ 103011454013527673 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206022908027055347) ^ 1312247821828378 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 206022908027055347) ^ 314 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_230109375452914961 : Nat.Prime 230109375452914961 := by
  apply lucas_primality 230109375452914961 (3 : ZMod 230109375452914961)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (38977, 1), (73796525981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (38977, 1), (73796525981, 1)] : List FactorBlock).map factorBlockValue).prod) = 230109375452914961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_38977
      · exact prime_ninetyEightCR_73796525981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230109375452914961) ^ 115054687726457480 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 230109375452914961) ^ 46021875090582992 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 230109375452914961) ^ 5903722078480 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 230109375452914961) ^ 3118160 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_307513519670110331 : Nat.Prime 307513519670110331 := by
  apply lucas_primality 307513519670110331 (6 : ZMod 307513519670110331)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18013, 1), (1707175482541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18013, 1), (1707175482541, 1)] : List FactorBlock).map factorBlockValue).prod) = 307513519670110331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_18013
      · exact prime_ninetyEightCR_1707175482541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 307513519670110331) ^ 153756759835055165 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 307513519670110331) ^ 61502703934022066 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 307513519670110331) ^ 17071754825410 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 307513519670110331) ^ 180130 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_592117395072158941 : Nat.Prime 592117395072158941 := by
  apply lucas_primality 592117395072158941 (2 : ZMod 592117395072158941)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (97, 1), (1667842361197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (97, 1), (1667842361197, 1)] : List FactorBlock).map factorBlockValue).prod) = 592117395072158941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_61
      · exact prime_ninetyEightCR_97
      · exact prime_ninetyEightCR_1667842361197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 592117395072158941) ^ 296058697536079470 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 592117395072158941) ^ 197372465024052980 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 592117395072158941) ^ 118423479014431788 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 592117395072158941) ^ 9706842542166540 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 592117395072158941) ^ 6104303041981020 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 592117395072158941) ^ 355020 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_650893475742842401 : Nat.Prime 650893475742842401 := by
  apply lucas_primality 650893475742842401 (7 : ZMod 650893475742842401)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (163, 1), (1663838128177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (163, 1), (1663838128177, 1)] : List FactorBlock).map factorBlockValue).prod) = 650893475742842401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_163
      · exact prime_ninetyEightCR_1663838128177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 650893475742842401) ^ 325446737871421200 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 650893475742842401) ^ 216964491914280800 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 650893475742842401) ^ 130178695148568480 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 650893475742842401) ^ 3993211507624800 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 650893475742842401) ^ 391200 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_841728001621930711 : Nat.Prime 841728001621930711 := by
  apply lucas_primality 841728001621930711 (3 : ZMod 841728001621930711)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (401, 1), (619, 1), (142902233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (401, 1), (619, 1), (142902233, 1)] : List FactorBlock).map factorBlockValue).prod) = 841728001621930711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_401
      · exact prime_ninetyEightCR_619
      · exact prime_ninetyEightCR_142902233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841728001621930711) ^ 420864000810965355 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 280576000540643570 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 168345600324386142 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 120246857374561530 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 7448920368335670 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 2099072323246710 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 1359819065625090 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 841728001621930711) ^ 5890236870 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_870440519352942301 : Nat.Prime 870440519352942301 := by
  apply lucas_primality 870440519352942301 (6 : ZMod 870440519352942301)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 2), (239, 1), (16553, 1), (14967427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 2), (239, 1), (16553, 1), (14967427, 1)] : List FactorBlock).map factorBlockValue).prod) = 870440519352942301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_239
      · exact prime_ninetyEightCR_16553
      · exact prime_ninetyEightCR_14967427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 870440519352942301) ^ 435220259676471150 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 290146839784314100 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 174088103870588460 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 124348645621848900 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 3642010541225700 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 52585061279100 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (6 : ZMod 870440519352942301) ^ 58155654900 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_924012841813427953 : Nat.Prime 924012841813427953 := by
  apply lucas_primality 924012841813427953 (5 : ZMod 924012841813427953)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (101, 1), (1049, 1), (2521, 1), (8008009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (101, 1), (1049, 1), (2521, 1), (8008009, 1)] : List FactorBlock).map factorBlockValue).prod) = 924012841813427953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_101
      · exact prime_ninetyEightCR_1049
      · exact prime_ninetyEightCR_2521
      · exact prime_ninetyEightCR_8008009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 924012841813427953) ^ 462006420906713976 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 924012841813427953) ^ 308004280604475984 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 924012841813427953) ^ 9148641998152752 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 924012841813427953) ^ 880851136142448 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 924012841813427953) ^ 366526315673712 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 924012841813427953) ^ 115386089328 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1182544326208977673 : Nat.Prime 1182544326208977673 := by
  apply lucas_primality 1182544326208977673 (5 : ZMod 1182544326208977673)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (49272680258707403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (49272680258707403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182544326208977673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_49272680258707403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1182544326208977673) ^ 591272163104488836 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182544326208977673) ^ 394181442069659224 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1182544326208977673) ^ 24 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1235686986449072393 : Nat.Prime 1235686986449072393 := by
  apply lucas_primality 1235686986449072393 (3 : ZMod 1235686986449072393)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (154460873306134049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (154460873306134049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235686986449072393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_154460873306134049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1235686986449072393) ^ 617843493224536196 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235686986449072393) ^ 8 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1661790126256258087 : Nat.Prime 1661790126256258087 := by
  apply lucas_primality 1661790126256258087 (3 : ZMod 1661790126256258087)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (29, 1), (4111, 1), (70398841003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (29, 1), (4111, 1), (70398841003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1661790126256258087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_4111
      · exact prime_ninetyEightCR_70398841003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1661790126256258087) ^ 830895063128129043 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1661790126256258087) ^ 553930042085419362 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1661790126256258087) ^ 151071829659659826 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1661790126256258087) ^ 57303107801939934 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1661790126256258087) ^ 404230145039226 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1661790126256258087) ^ 23605362 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1769007715370943457 : Nat.Prime 1769007715370943457 := by
  apply lucas_primality 1769007715370943457 (10 : ZMod 1769007715370943457)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (3191, 1), (5774730085171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (3191, 1), (5774730085171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769007715370943457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_3191
      · exact prime_ninetyEightCR_5774730085171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1769007715370943457) ^ 884503857685471728 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1769007715370943457) ^ 589669238456981152 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1769007715370943457) ^ 554374088176416 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 1769007715370943457) ^ 306336 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1792918411691793173 : Nat.Prime 1792918411691793173 := by
  apply lucas_primality 1792918411691793173 (2 : ZMod 1792918411691793173)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (88158337, 1), (5084369989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (88158337, 1), (5084369989, 1)] : List FactorBlock).map factorBlockValue).prod) = 1792918411691793173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_88158337
      · exact prime_ninetyEightCR_5084369989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1792918411691793173) ^ 896459205845896586 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1792918411691793173) ^ 20337479956 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 1792918411691793173) ^ 352633348 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2836020119598216029 : Nat.Prime 2836020119598216029 := by
  apply lucas_primality 2836020119598216029 (2 : ZMod 2836020119598216029)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (25041431, 1), (146700929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (25041431, 1), (146700929, 1)] : List FactorBlock).map factorBlockValue).prod) = 2836020119598216029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_193
      · exact prime_ninetyEightCR_25041431
      · exact prime_ninetyEightCR_146700929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2836020119598216029) ^ 1418010059799108014 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836020119598216029) ^ 14694404764757596 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836020119598216029) ^ 113253117188 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2836020119598216029) ^ 19331984732 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3133139167501653209 : Nat.Prime 3133139167501653209 := by
  apply lucas_primality 3133139167501653209 (3 : ZMod 3133139167501653209)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (20612757680931929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (20612757680931929, 1)] : List FactorBlock).map factorBlockValue).prod) = 3133139167501653209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_20612757680931929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3133139167501653209) ^ 1566569583750826604 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133139167501653209) ^ 164902061447455432 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133139167501653209) ^ 152 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3170349736822212883 : Nat.Prime 3170349736822212883 := by
  apply lucas_primality 3170349736822212883 (2 : ZMod 3170349736822212883)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (103, 1), (5657, 1), (18507017693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (103, 1), (5657, 1), (18507017693, 1)] : List FactorBlock).map factorBlockValue).prod) = 3170349736822212883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_103
      · exact prime_ninetyEightCR_5657
      · exact prime_ninetyEightCR_18507017693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3170349736822212883) ^ 1585174868411106441 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3170349736822212883) ^ 1056783245607404294 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3170349736822212883) ^ 452907105260316126 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3170349736822212883) ^ 30780094532254494 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3170349736822212883) ^ 560429509779426 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 3170349736822212883) ^ 171305274 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3785223103918077641 : Nat.Prime 3785223103918077641 := by
  apply lucas_primality 3785223103918077641 (3 : ZMod 3785223103918077641)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (13, 1), (311, 1), (367, 1), (9110949623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (13, 1), (311, 1), (367, 1), (9110949623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3785223103918077641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_311
      · exact prime_ninetyEightCR_367
      · exact prime_ninetyEightCR_9110949623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3785223103918077641) ^ 1892611551959038820 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 757044620783615528 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 540746157702582520 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 291171007993698280 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 12171135382373240 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 10313959411220920 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3785223103918077641) ^ 415458680 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_3856151555469391459 : Nat.Prime 3856151555469391459 := by
  apply lucas_primality 3856151555469391459 (3 : ZMod 3856151555469391459)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (91813132273080749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (91813132273080749, 1)] : List FactorBlock).map factorBlockValue).prod) = 3856151555469391459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_91813132273080749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3856151555469391459) ^ 1928075777734695729 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3856151555469391459) ^ 1285383851823130486 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3856151555469391459) ^ 550878793638484494 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 3856151555469391459) ^ 42 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4083279869590835647 : Nat.Prime 4083279869590835647 := by
  apply lucas_primality 4083279869590835647 (3 : ZMod 4083279869590835647)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1607, 1), (4374571, 1), (96806953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1607, 1), (4374571, 1), (96806953, 1)] : List FactorBlock).map factorBlockValue).prod) = 4083279869590835647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_1607
      · exact prime_ninetyEightCR_4374571
      · exact prime_ninetyEightCR_96806953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4083279869590835647) ^ 2041639934795417823 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083279869590835647) ^ 1361093289863611882 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083279869590835647) ^ 2540933335152978 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083279869590835647) ^ 933412640826 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083279869590835647) ^ 42179613582 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4315913221926637343 : Nat.Prime 4315913221926637343 := by
  apply lucas_primality 4315913221926637343 (5 : ZMod 4315913221926637343)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 2), (19, 2), (17903, 1), (105031403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 2), (19, 2), (17903, 1), (105031403, 1)] : List FactorBlock).map factorBlockValue).prod) = 4315913221926637343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_17903
      · exact prime_ninetyEightCR_105031403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4315913221926637343) ^ 2157956610963318671 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 4315913221926637343) ^ 392355747447876122 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 4315913221926637343) ^ 253877248348625726 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 4315913221926637343) ^ 227153327469823018 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 4315913221926637343) ^ 241072067358914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 4315913221926637343) ^ 41091645914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_4423612398618637657 : Nat.Prime 4423612398618637657 := by
  apply lucas_primality 4423612398618637657 (7 : ZMod 4423612398618637657)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (16110221, 1), (1271223221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (16110221, 1), (1271223221, 1)] : List FactorBlock).map factorBlockValue).prod) = 4423612398618637657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_16110221
      · exact prime_ninetyEightCR_1271223221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4423612398618637657) ^ 2211806199309318828 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 4423612398618637657) ^ 1474537466206212552 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 4423612398618637657) ^ 274584215736 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 4423612398618637657) ^ 3479807736 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8399598092844371971 : Nat.Prime 8399598092844371971 := by
  apply lucas_primality 8399598092844371971 (2 : ZMod 8399598092844371971)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (199, 1), (659, 1), (2135004331939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (199, 1), (659, 1), (2135004331939, 1)] : List FactorBlock).map factorBlockValue).prod) = 8399598092844371971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_199
      · exact prime_ninetyEightCR_659
      · exact prime_ninetyEightCR_2135004331939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8399598092844371971) ^ 4199799046422185985 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8399598092844371971) ^ 2799866030948123990 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8399598092844371971) ^ 1679919618568874394 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8399598092844371971) ^ 42209035642434030 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8399598092844371971) ^ 12745975861675830 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 8399598092844371971) ^ 3934230 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_9688696171250312357 : Nat.Prime 9688696171250312357 := by
  apply lucas_primality 9688696171250312357 (2 : ZMod 9688696171250312357)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (241, 1), (2865659, 1), (17276977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (241, 1), (2865659, 1), (17276977, 1)] : List FactorBlock).map factorBlockValue).prod) = 9688696171250312357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_29
      · exact prime_ninetyEightCR_241
      · exact prime_ninetyEightCR_2865659
      · exact prime_ninetyEightCR_17276977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9688696171250312357) ^ 4844348085625156178 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9688696171250312357) ^ 1384099453035758908 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9688696171250312357) ^ 334092971422424564 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9688696171250312357) ^ 40202058801868516 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9688696171250312357) ^ 3380966183084 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 9688696171250312357) ^ 560786541028 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_23221234202171814271 : Nat.Prime 23221234202171814271 := by
  apply lucas_primality 23221234202171814271 (7 : ZMod 23221234202171814271)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 2), (3574657, 1), (85216757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 2), (3574657, 1), (85216757, 1)] : List FactorBlock).map factorBlockValue).prod) = 23221234202171814271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_3574657
      · exact prime_ninetyEightCR_85216757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23221234202171814271) ^ 11610617101085907135 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 7740411400723938090 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 4644246840434362854 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 3317319171738830610 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 2111021291106528570 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 6496073386110 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 23221234202171814271) ^ 272496103110 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_35107596586493078537 : Nat.Prime 35107596586493078537 := by
  apply lucas_primality 35107596586493078537 (3 : ZMod 35107596586493078537)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (711499, 1), (125875363667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (711499, 1), (125875363667, 1)] : List FactorBlock).map factorBlockValue).prod) = 35107596586493078537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_711499
      · exact prime_ninetyEightCR_125875363667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35107596586493078537) ^ 17553798293246539268 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 35107596586493078537) ^ 5015370940927582648 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 35107596586493078537) ^ 49343142557464 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 35107596586493078537) ^ 278907608 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_59087715390938998409 : Nat.Prime 59087715390938998409 := by
  apply lucas_primality 59087715390938998409 (3 : ZMod 59087715390938998409)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (110777, 1), (2898876914831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (110777, 1), (2898876914831, 1)] : List FactorBlock).map factorBlockValue).prod) = 59087715390938998409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_110777
      · exact prime_ninetyEightCR_2898876914831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59087715390938998409) ^ 29543857695469499204 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 59087715390938998409) ^ 2569031103953869496 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 59087715390938998409) ^ 533393352328904 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 59087715390938998409) ^ 20382968 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_108366471390484062937 : Nat.Prime 108366471390484062937 := by
  apply lucas_primality 108366471390484062937 (5 : ZMod 108366471390484062937)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (193, 1), (77351, 1), (100818259141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (193, 1), (77351, 1), (100818259141, 1)] : List FactorBlock).map factorBlockValue).prod) = 108366471390484062937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_193
      · exact prime_ninetyEightCR_77351
      · exact prime_ninetyEightCR_100818259141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 108366471390484062937) ^ 54183235695242031468 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108366471390484062937) ^ 36122157130161354312 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108366471390484062937) ^ 561484307722715352 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108366471390484062937) ^ 1400970529023336 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 108366471390484062937) ^ 1074869496 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_211892924968791267997 : Nat.Prime 211892924968791267997 := by
  apply lucas_primality 211892924968791267997 (2 : ZMod 211892924968791267997)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1093, 1), (243533, 1), (7370801573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1093, 1), (243533, 1), (7370801573, 1)] : List FactorBlock).map factorBlockValue).prod) = 211892924968791267997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_1093
      · exact prime_ninetyEightCR_243533
      · exact prime_ninetyEightCR_7370801573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211892924968791267997) ^ 105946462484395633998 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 211892924968791267997) ^ 70630974989597089332 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 211892924968791267997) ^ 193863609303560172 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 211892924968791267997) ^ 870078900883212 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 211892924968791267997) ^ 28747609452 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_239713832280023661041 : Nat.Prime 239713832280023661041 := by
  apply lucas_primality 239713832280023661041 (3 : ZMod 239713832280023661041)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (67, 1), (2917, 1), (111373, 1), (10589333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (67, 1), (2917, 1), (111373, 1), (10589333, 1)] : List FactorBlock).map factorBlockValue).prod) = 239713832280023661041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_67
      · exact prime_ninetyEightCR_2917
      · exact prime_ninetyEightCR_111373
      · exact prime_ninetyEightCR_10589333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 239713832280023661041) ^ 119856916140011830520 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 47942766456004732208 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 18439525560001820080 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 3577818392239159120 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 82178207843683120 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 2152351398274480 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 239713832280023661041) ^ 22637292856880 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_706453368963688017361 : Nat.Prime 706453368963688017361 := by
  apply lucas_primality 706453368963688017361 (22 : ZMod 706453368963688017361)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (13, 1), (324647, 1), (232485706883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (13, 1), (324647, 1), (232485706883, 1)] : List FactorBlock).map factorBlockValue).prod) = 706453368963688017361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_324647
      · exact prime_ninetyEightCR_232485706883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 706453368963688017361) ^ 353226684481844008680 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (22 : ZMod 706453368963688017361) ^ 235484456321229339120 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (22 : ZMod 706453368963688017361) ^ 141290673792737603472 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (22 : ZMod 706453368963688017361) ^ 54342566843360616720 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (22 : ZMod 706453368963688017361) ^ 2176066216424880 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (22 : ZMod 706453368963688017361) ^ 3038695920 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1163074014733227568607 : Nat.Prime 1163074014733227568607 := by
  apply lucas_primality 1163074014733227568607 (5 : ZMod 1163074014733227568607)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53, 1), (691, 1), (5077789, 1), (164586871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53, 1), (691, 1), (5077789, 1), (164586871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163074014733227568607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_53
      · exact prime_ninetyEightCR_691
      · exact prime_ninetyEightCR_5077789
      · exact prime_ninetyEightCR_164586871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1163074014733227568607) ^ 581537007366613784303 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163074014733227568607) ^ 61214421828064608874 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163074014733227568607) ^ 21944792730815614502 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163074014733227568607) ^ 1683175129859953066 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163074014733227568607) ^ 229051269112054 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163074014733227568607) ^ 7066626928786 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_2009731607678138594629 : Nat.Prime 2009731607678138594629 := by
  apply lucas_primality 2009731607678138594629 (2 : ZMod 2009731607678138594629)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11779, 1), (290169869888089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11779, 1), (290169869888089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009731607678138594629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11779
      · exact prime_ninetyEightCR_290169869888089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2009731607678138594629) ^ 1004865803839069297314 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009731607678138594629) ^ 669910535892712864876 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009731607678138594629) ^ 287104515382591227804 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009731607678138594629) ^ 170619883494196332 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 2009731607678138594629) ^ 6926052 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8196812856155301983273 : Nat.Prime 8196812856155301983273 := by
  apply lucas_primality 8196812856155301983273 (3 : ZMod 8196812856155301983273)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (1637, 1), (29569, 1), (329473, 1), (468953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (1637, 1), (29569, 1), (329473, 1), (468953, 1)] : List FactorBlock).map factorBlockValue).prod) = 8196812856155301983273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_137
      · exact prime_ninetyEightCR_1637
      · exact prime_ninetyEightCR_29569
      · exact prime_ninetyEightCR_329473
      · exact prime_ninetyEightCR_468953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8196812856155301983273) ^ 4098406428077650991636 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196812856155301983273) ^ 59830750774856218856 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196812856155301983273) ^ 5007216161365486856 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196812856155301983273) ^ 277209674191054888 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196812856155301983273) ^ 24878557138689064 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196812856155301983273) ^ 17478964536222824 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_14846183488557157117151 : Nat.Prime 14846183488557157117151 := by
  apply lucas_primality 14846183488557157117151 (11 : ZMod 14846183488557157117151)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (11, 1), (3856151555469391459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (11, 1), (3856151555469391459, 1)] : List FactorBlock).map factorBlockValue).prod) = 14846183488557157117151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_3856151555469391459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14846183488557157117151) ^ 7423091744278578558575 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 14846183488557157117151) ^ 2969236697711431423430 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 14846183488557157117151) ^ 2120883355508165302450 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 14846183488557157117151) ^ 1349653044414287010650 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 14846183488557157117151) ^ 3850 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_17952887429784472887571 : Nat.Prime 17952887429784472887571 := by
  apply lucas_primality 17952887429784472887571 (3 : ZMod 17952887429784472887571)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (191, 1), (3133139167501653209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (191, 1), (3133139167501653209, 1)] : List FactorBlock).map factorBlockValue).prod) = 17952887429784472887571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_191
      · exact prime_ninetyEightCR_3133139167501653209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17952887429784472887571) ^ 8976443714892236443785 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 17952887429784472887571) ^ 5984295809928157629190 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 17952887429784472887571) ^ 3590577485956894577514 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 17952887429784472887571) ^ 93994175025049596270 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 17952887429784472887571) ^ 5730 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_30195892966352924007403 : Nat.Prime 30195892966352924007403 := by
  apply lucas_primality 30195892966352924007403 (2 : ZMod 30195892966352924007403)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1523, 1), (11447, 1), (288672252320107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1523, 1), (11447, 1), (288672252320107, 1)] : List FactorBlock).map factorBlockValue).prod) = 30195892966352924007403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_1523
      · exact prime_ninetyEightCR_11447
      · exact prime_ninetyEightCR_288672252320107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30195892966352924007403) ^ 15097946483176462003701 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30195892966352924007403) ^ 10065297655450974669134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30195892966352924007403) ^ 19826587633849588974 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30195892966352924007403) ^ 2637887041701137766 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30195892966352924007403) ^ 104602686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_45141919973380008499939 : Nat.Prime 45141919973380008499939 := by
  apply lucas_primality 45141919973380008499939 (2 : ZMod 45141919973380008499939)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2039, 1), (2357, 1), (233609, 1), (957335927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2039, 1), (2357, 1), (233609, 1), (957335927, 1)] : List FactorBlock).map factorBlockValue).prod) = 45141919973380008499939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_2039
      · exact prime_ninetyEightCR_2357
      · exact prime_ninetyEightCR_233609
      · exact prime_ninetyEightCR_957335927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45141919973380008499939) ^ 22570959986690004249969 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 15047306657793336166646 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 6448845710482858357134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 22139244714752333742 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 19152278308604161434 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 193237075512416082 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 45141919973380008499939) ^ 47153688376494 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_142861913374561776722441 : Nat.Prime 142861913374561776722441 := by
  apply lucas_primality 142861913374561776722441 (3 : ZMod 142861913374561776722441)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (67, 1), (4993, 1), (10676283616059631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (67, 1), (4993, 1), (10676283616059631, 1)] : List FactorBlock).map factorBlockValue).prod) = 142861913374561776722441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_67
      · exact prime_ninetyEightCR_4993
      · exact prime_ninetyEightCR_10676283616059631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 142861913374561776722441) ^ 71430956687280888361220 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142861913374561776722441) ^ 28572382674912355344488 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142861913374561776722441) ^ 2132267363799429503320 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142861913374561776722441) ^ 28612440091039811080 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 142861913374561776722441) ^ 13381240 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_221516814473226899311933 : Nat.Prime 221516814473226899311933 := by
  apply lucas_primality 221516814473226899311933 (2 : ZMod 221516814473226899311933)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (107, 1), (4423612398618637657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (107, 1), (4423612398618637657, 1)] : List FactorBlock).map factorBlockValue).prod) = 221516814473226899311933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_107
      · exact prime_ninetyEightCR_4423612398618637657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221516814473226899311933) ^ 110758407236613449655966 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 221516814473226899311933) ^ 73838938157742299770644 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 221516814473226899311933) ^ 17039754959478992254764 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 221516814473226899311933) ^ 2070250602553522423476 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 221516814473226899311933) ^ 50076 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_917124359956911925847081 : Nat.Prime 917124359956911925847081 := by
  apply lucas_primality 917124359956911925847081 (3 : ZMod 917124359956911925847081)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (997, 1), (1769007715370943457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (997, 1), (1769007715370943457, 1)] : List FactorBlock).map factorBlockValue).prod) = 917124359956911925847081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_997
      · exact prime_ninetyEightCR_1769007715370943457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 917124359956911925847081) ^ 458562179978455962923540 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 917124359956911925847081) ^ 183424871991382385169416 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 917124359956911925847081) ^ 70548027688993225065160 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 917124359956911925847081) ^ 919884011992890597640 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 917124359956911925847081) ^ 518440 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1525887379885377479766017 : Nat.Prime 1525887379885377479766017 := by
  apply lucas_primality 1525887379885377479766017 (3 : ZMod 1525887379885377479766017)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (13, 1), (61357, 1), (467041060583431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (13, 1), (61357, 1), (467041060583431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1525887379885377479766017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_13
      · exact prime_ninetyEightCR_61357
      · exact prime_ninetyEightCR_467041060583431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1525887379885377479766017) ^ 762943689942688739883008 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525887379885377479766017) ^ 117375952298875190751232 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525887379885377479766017) ^ 24869002393946533888 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525887379885377479766017) ^ 3267137536 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8754224000156901958149863 : Nat.Prime 8754224000156901958149863 := by
  apply lucas_primality 8754224000156901958149863 (5 : ZMod 8754224000156901958149863)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (2083, 1), (145193, 1), (149204175234217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (2083, 1), (145193, 1), (149204175234217, 1)] : List FactorBlock).map factorBlockValue).prod) = 8754224000156901958149863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_97
      · exact prime_ninetyEightCR_2083
      · exact prime_ninetyEightCR_145193
      · exact prime_ninetyEightCR_149204175234217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8754224000156901958149863) ^ 4377112000078450979074931 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8754224000156901958149863) ^ 90249731960380432558246 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8754224000156901958149863) ^ 4202699952067643762914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8754224000156901958149863) ^ 60293705620497558134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 8754224000156901958149863) ^ 58672781686 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_16644469852331072750483183 : Nat.Prime 16644469852331072750483183 := by
  apply lucas_primality 16644469852331072750483183 (5 : ZMod 16644469852331072750483183)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (24019, 1), (1182544326208977673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (24019, 1), (1182544326208977673, 1)] : List FactorBlock).map factorBlockValue).prod) = 16644469852331072750483183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_293
      · exact prime_ninetyEightCR_24019
      · exact prime_ninetyEightCR_1182544326208977673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16644469852331072750483183) ^ 8322234926165536375241591 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 16644469852331072750483183) ^ 56807064342426869455574 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 16644469852331072750483183) ^ 692970975158460916378 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 16644469852331072750483183) ^ 14075134 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_18286324911943907420472449 : Nat.Prime 18286324911943907420472449 := by
  apply lucas_primality 18286324911943907420472449 (3 : ZMod 18286324911943907420472449)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (142861913374561776722441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (142861913374561776722441, 1)] : List FactorBlock).map factorBlockValue).prod) = 18286324911943907420472449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_142861913374561776722441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 18286324911943907420472449) ^ 9143162455971953710236224 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 18286324911943907420472449) ^ 128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_26957225370422661101934257 : Nat.Prime 26957225370422661101934257 := by
  apply lucas_primality 26957225370422661101934257 (3 : ZMod 26957225370422661101934257)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (172721, 1), (351197789, 1), (2525024549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (172721, 1), (351197789, 1), (2525024549, 1)] : List FactorBlock).map factorBlockValue).prod) = 26957225370422661101934257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_11
      · exact prime_ninetyEightCR_172721
      · exact prime_ninetyEightCR_351197789
      · exact prime_ninetyEightCR_2525024549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26957225370422661101934257) ^ 13478612685211330550967128 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26957225370422661101934257) ^ 2450656851856605554721296 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26957225370422661101934257) ^ 156073814825195900336 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26957225370422661101934257) ^ 76757958662497904 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 26957225370422661101934257) ^ 10676025063240944 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_30979185733175560806447443 : Nat.Prime 30979185733175560806447443 := by
  apply lucas_primality 30979185733175560806447443 (2 : ZMod 30979185733175560806447443)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (53, 1), (207287, 1), (4698101, 1), (6385161113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (53, 1), (207287, 1), (4698101, 1), (6385161113, 1)] : List FactorBlock).map factorBlockValue).prod) = 30979185733175560806447443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_47
      · exact prime_ninetyEightCR_53
      · exact prime_ninetyEightCR_207287
      · exact prime_ninetyEightCR_4698101
      · exact prime_ninetyEightCR_6385161113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30979185733175560806447443) ^ 15489592866587780403223721 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30979185733175560806447443) ^ 659131611344160868222286 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30979185733175560806447443) ^ 584512938361803034083914 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30979185733175560806447443) ^ 149450692678149429566 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30979185733175560806447443) ^ 6593980362102807242 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 30979185733175560806447443) ^ 4851746915219234 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_68314949671035729608557451 : Nat.Prime 68314949671035729608557451 := by
  apply lucas_primality 68314949671035729608557451 (2 : ZMod 68314949671035729608557451)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 3), (40433, 1), (98518017202897771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 3), (40433, 1), (98518017202897771, 1)] : List FactorBlock).map factorBlockValue).prod) = 68314949671035729608557451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_40433
      · exact prime_ninetyEightCR_98518017202897771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68314949671035729608557451) ^ 34157474835517864804278725 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 68314949671035729608557451) ^ 13662989934207145921711490 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 68314949671035729608557451) ^ 9759278524433675658365350 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 68314949671035729608557451) ^ 1689583995029696772650 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 68314949671035729608557451) ^ 693425950 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_157207808198204338420778069 : Nat.Prime 157207808198204338420778069 := by
  apply lucas_primality 157207808198204338420778069 (2 : ZMod 157207808198204338420778069)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2238631, 1), (924012841813427953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2238631, 1), (924012841813427953, 1)] : List FactorBlock).map factorBlockValue).prod) = 157207808198204338420778069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_2238631
      · exact prime_ninetyEightCR_924012841813427953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 157207808198204338420778069) ^ 78603904099102169210389034 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157207808198204338420778069) ^ 8274095168326544127409372 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157207808198204338420778069) ^ 70224975977820524428 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 157207808198204338420778069) ^ 170135956 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_170636457499376432129769421 : Nat.Prime 170636457499376432129769421 := by
  apply lucas_primality 170636457499376432129769421 (2 : ZMod 170636457499376432129769421)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (45141919973380008499939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (45141919973380008499939, 1)] : List FactorBlock).map factorBlockValue).prod) = 170636457499376432129769421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_45141919973380008499939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170636457499376432129769421) ^ 85318228749688216064884710 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 170636457499376432129769421) ^ 56878819166458810709923140 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 170636457499376432129769421) ^ 34127291499875286425953884 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 170636457499376432129769421) ^ 24376636785625204589967060 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 170636457499376432129769421) ^ 3780 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_172670871299667060232657879 : Nat.Prime 172670871299667060232657879 := by
  apply lucas_primality 172670871299667060232657879 (3 : ZMod 172670871299667060232657879)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (229, 1), (17952887429784472887571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (229, 1), (17952887429784472887571, 1)] : List FactorBlock).map factorBlockValue).prod) = 172670871299667060232657879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_229
      · exact prime_ninetyEightCR_17952887429784472887571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 172670871299667060232657879) ^ 86335435649833530116328939 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 172670871299667060232657879) ^ 57556957099889020077552626 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 172670871299667060232657879) ^ 24667267328523865747522554 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 172670871299667060232657879) ^ 754021272050947861277982 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 172670871299667060232657879) ^ 9618 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_185676529875122752269412559 : Nat.Prime 185676529875122752269412559 := by
  apply lucas_primality 185676529875122752269412559 (11 : ZMod 185676529875122752269412559)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (4153, 1), (46237, 1), (10483717, 1), (2427205493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (4153, 1), (46237, 1), (10483717, 1), (2427205493, 1)] : List FactorBlock).map factorBlockValue).prod) = 185676529875122752269412559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_19
      · exact prime_ninetyEightCR_4153
      · exact prime_ninetyEightCR_46237
      · exact prime_ninetyEightCR_10483717
      · exact prime_ninetyEightCR_2427205493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 185676529875122752269412559) ^ 92838264937561376134706279 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 185676529875122752269412559) ^ 9772448940795934329969082 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 185676529875122752269412559) ^ 44709012731789730861886 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 185676529875122752269412559) ^ 4015756426133242906534 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 185676529875122752269412559) ^ 17710944493744227574 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (11 : ZMod 185676529875122752269412559) ^ 76498067596917206 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_206896704717993923957345423 : Nat.Prime 206896704717993923957345423 := by
  apply lucas_primality 206896704717993923957345423 (5 : ZMod 206896704717993923957345423)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467, 1), (221516814473226899311933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467, 1), (221516814473226899311933, 1)] : List FactorBlock).map factorBlockValue).prod) = 206896704717993923957345423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_467
      · exact prime_ninetyEightCR_221516814473226899311933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 206896704717993923957345423) ^ 103448352358996961978672711 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 206896704717993923957345423) ^ 443033628946453798623866 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 206896704717993923957345423) ^ 934 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_212201748428711716879328639 : Nat.Prime 212201748428711716879328639 := by
  apply lucas_primality 212201748428711716879328639 (7 : ZMod 212201748428711716879328639)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (217909, 1), (1661790126256258087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (217909, 1), (1661790126256258087, 1)] : List FactorBlock).map factorBlockValue).prod) = 212201748428711716879328639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_293
      · exact prime_ninetyEightCR_217909
      · exact prime_ninetyEightCR_1661790126256258087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 212201748428711716879328639) ^ 106100874214355858439664319 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 212201748428711716879328639) ^ 724238049244749886960166 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 212201748428711716879328639) ^ 973809013986167238982 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 212201748428711716879328639) ^ 127694674 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_240877660378537624565724401 : Nat.Prime 240877660378537624565724401 := by
  apply lucas_primality 240877660378537624565724401 (3 : ZMod 240877660378537624565724401)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (23, 1), (1097, 1), (2381, 1), (5743, 1), (1745435712707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (23, 1), (1097, 1), (2381, 1), (5743, 1), (1745435712707, 1)] : List FactorBlock).map factorBlockValue).prod) = 240877660378537624565724401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_1097
      · exact prime_ninetyEightCR_2381
      · exact prime_ninetyEightCR_5743
      · exact prime_ninetyEightCR_1745435712707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 240877660378537624565724401) ^ 120438830189268812282862200 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 48175532075707524913144880 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 10472941755588592372422800 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 219578541821820988665200 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 101166594027105260212400 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 41942827856266345910800 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 240877660378537624565724401) ^ 138004315269200 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_377401155185917255427079599 : Nat.Prime 377401155185917255427079599 := by
  apply lucas_primality 377401155185917255427079599 (7 : ZMod 377401155185917255427079599)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (26957225370422661101934257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (26957225370422661101934257, 1)] : List FactorBlock).map factorBlockValue).prod) = 377401155185917255427079599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_26957225370422661101934257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 377401155185917255427079599) ^ 188700577592958627713539799 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 377401155185917255427079599) ^ 53914450740845322203868514 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 377401155185917255427079599) ^ 14 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_728692796491047782491279477 : Nat.Prime 728692796491047782491279477 := by
  apply lucas_primality 728692796491047782491279477 (2 : ZMod 728692796491047782491279477)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (5134487, 1), (99384626579637391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (5134487, 1), (99384626579637391, 1)] : List FactorBlock).map factorBlockValue).prod) = 728692796491047782491279477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_7
      · exact prime_ninetyEightCR_17
      · exact prime_ninetyEightCR_5134487
      · exact prime_ninetyEightCR_99384626579637391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 728692796491047782491279477) ^ 364346398245523891245639738 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 728692796491047782491279477) ^ 242897598830349260830426492 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 728692796491047782491279477) ^ 104098970927292540355897068 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 728692796491047782491279477) ^ 42864282146532222499487028 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 728692796491047782491279477) ^ 141921246755722194348 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 728692796491047782491279477) ^ 7332047436 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1043803194973663039784805737 : Nat.Prime 1043803194973663039784805737 := by
  apply lucas_primality 1043803194973663039784805737 (3 : ZMod 1043803194973663039784805737)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (615761, 1), (211892924968791267997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (615761, 1), (211892924968791267997, 1)] : List FactorBlock).map factorBlockValue).prod) = 1043803194973663039784805737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_615761
      · exact prime_ninetyEightCR_211892924968791267997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1043803194973663039784805737) ^ 521901597486831519892402868 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1043803194973663039784805737) ^ 1695143399750330143976 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 1043803194973663039784805737) ^ 4926088 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_1182266884102822422613402417 : Nat.Prime 1182266884102822422613402417 := by
  apply lucas_primality 1182266884102822422613402417 (7 : ZMod 1182266884102822422613402417)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (819178583, 1), (1307277727938113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (819178583, 1), (1307277727938113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822422613402417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_23
      · exact prime_ninetyEightCR_819178583
      · exact prime_ninetyEightCR_1307277727938113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1182266884102822422613402417) ^ 591133442051411211306701208 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1182266884102822422613402417) ^ 394088961367607474204467472 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1182266884102822422613402417) ^ 51402908004470540113626192 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1182266884102822422613402417) ^ 1443234611643676752 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (7 : ZMod 1182266884102822422613402417) ^ 904373155632 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5037484984438112931135366821 : Nat.Prime 5037484984438112931135366821 := by
  apply lucas_primality 5037484984438112931135366821 (2 : ZMod 5037484984438112931135366821)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (41999318267, 1), (53071710418271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (41999318267, 1), (53071710418271, 1)] : List FactorBlock).map factorBlockValue).prod) = 5037484984438112931135366821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_5
      · exact prime_ninetyEightCR_113
      · exact prime_ninetyEightCR_41999318267
      · exact prime_ninetyEightCR_53071710418271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5037484984438112931135366821) ^ 2518742492219056465567683410 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5037484984438112931135366821) ^ 1007496996887622586227073364 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5037484984438112931135366821) ^ 44579513136620468417127140 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5037484984438112931135366821) ^ 119942065545292460 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 5037484984438112931135366821) ^ 94918459283420 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_5266461574639845337096065313 : Nat.Prime 5266461574639845337096065313 := by
  apply lucas_primality 5266461574639845337096065313 (10 : ZMod 5266461574639845337096065313)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (18286324911943907420472449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (18286324911943907420472449, 1)] : List FactorBlock).map factorBlockValue).prod) = 5266461574639845337096065313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_18286324911943907420472449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 5266461574639845337096065313) ^ 2633230787319922668548032656 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 5266461574639845337096065313) ^ 1755487191546615112365355104 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 5266461574639845337096065313) ^ 288 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_8912473434005892108931802833 : Nat.Prime 8912473434005892108931802833 := by
  apply lucas_primality 8912473434005892108931802833 (10 : ZMod 8912473434005892108931802833)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (185676529875122752269412559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (185676529875122752269412559, 1)] : List FactorBlock).map factorBlockValue).prod) = 8912473434005892108931802833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_185676529875122752269412559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 8912473434005892108931802833) ^ 4456236717002946054465901416 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 8912473434005892108931802833) ^ 2970824478001964036310600944 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (10 : ZMod 8912473434005892108931802833) ^ 48 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_23172430928415319483222687367 : Nat.Prime 23172430928415319483222687367 := by
  apply lucas_primality 23172430928415319483222687367 (5 : ZMod 23172430928415319483222687367)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (373, 1), (503, 1), (119106470929, 1), (518476918033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (373, 1), (503, 1), (119106470929, 1), (518476918033, 1)] : List FactorBlock).map factorBlockValue).prod) = 23172430928415319483222687367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_373
      · exact prime_ninetyEightCR_503
      · exact prime_ninetyEightCR_119106470929
      · exact prime_ninetyEightCR_518476918033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23172430928415319483222687367) ^ 11586215464207659741611343683 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 23172430928415319483222687367) ^ 62124479700845360544832942 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 23172430928415319483222687367) ^ 46068451149931052650542122 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 23172430928415319483222687367) ^ 194552241768866854 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (5 : ZMod 23172430928415319483222687367) ^ 44693273938456102 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_28965538660519149354028359203 : Nat.Prime 28965538660519149354028359203 := by
  apply lucas_primality 28965538660519149354028359203 (2 : ZMod 28965538660519149354028359203)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (15903637, 1), (4315913221926637343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (15903637, 1), (4315913221926637343, 1)] : List FactorBlock).map factorBlockValue).prod) = 28965538660519149354028359203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_211
      · exact prime_ninetyEightCR_15903637
      · exact prime_ninetyEightCR_4315913221926637343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28965538660519149354028359203) ^ 14482769330259574677014179601 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28965538660519149354028359203) ^ 137277434410043361867432982 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28965538660519149354028359203) ^ 1821315379653040958746 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (2 : ZMod 28965538660519149354028359203) ^ 6711334814 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem prime_ninetyEightCR_38620718214025532472037812283 : Nat.Prime 38620718214025532472037812283 := by
  apply lucas_primality 38620718214025532472037812283 (3 : ZMod 38620718214025532472037812283)
  · rw [← ninetyEightCRFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (3206363, 1), (8399598092844371971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (3206363, 1), (8399598092844371971, 1)] : List FactorBlock).map factorBlockValue).prod) = 38620718214025532472037812283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyEightCR_2
      · exact prime_ninetyEightCR_3
      · exact prime_ninetyEightCR_239
      · exact prime_ninetyEightCR_3206363
      · exact prime_ninetyEightCR_8399598092844371971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38620718214025532472037812283) ^ 19310359107012766236018906141 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38620718214025532472037812283) ^ 12873572738008510824012604094 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38620718214025532472037812283) ^ 161592963238600554276308838 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38620718214025532472037812283) ^ 12045023665138829406414 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide
    · change (3 : ZMod 38620718214025532472037812283) ^ 4597924542 ≠ 1
      rw [← ninetyEightCRFastPow_eq_pow]
      decide

private theorem phi_ninetyEightCR_115862154642076597416113436800 : Nat.totient 115862154642076597416113436800 = 43881574216496475891653038080 := by
  rw [← show ((([(2, 7), (5, 2), (19, 1), (1823, 1), (457924459, 1), (2282745586103, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_19, prime_ninetyEightCR_1823, prime_ninetyEightCR_457924459, prime_ninetyEightCR_2282745586103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436801 : Nat.totient 115862154642076597416113436801 = 76183334422372883625240585600 := by
  rw [← show ((([(3, 3), (73, 1), (556892591, 1), (105556148725735541, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_73, prime_ninetyEightCR_556892591, prime_ninetyEightCR_105556148725735541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436802 : Nat.totient 115862154642076597416113436802 = 57930073608241468089560361600 := by
  rw [← show ((([(2, 1), (60937, 1), (1092173, 1), (870440519352942301, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_60937, prime_ninetyEightCR_1092173, prime_ninetyEightCR_870440519352942301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436803 : Nat.totient 115862154642076597416113436803 = 86278734377404250400465684480 := by
  rw [← show ((([(7, 1), (13, 1), (17, 1), (2027609581, 1), (36937453561749229, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7, prime_ninetyEightCR_13, prime_ninetyEightCR_17, prime_ninetyEightCR_2027609581, prime_ninetyEightCR_36937453561749229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436804 : Nat.totient 115862154642076597416113436804 = 38531475920114485543428710400 := by
  rw [← show ((([(2, 2), (3, 1), (839, 1), (937, 1), (18869, 1), (650893475742842401, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_839, prime_ninetyEightCR_937, prime_ninetyEightCR_18869, prime_ninetyEightCR_650893475742842401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436805 : Nat.totient 115862154642076597416113436805 = 92654706817660650325058139408 := by
  rw [← show ((([(5, 1), (2647, 1), (8754224000156901958149863, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_2647, prime_ninetyEightCR_8754224000156901958149863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436806 : Nat.totient 115862154642076597416113436806 = 57926128902137453738776618560 := by
  rw [← show ((([(2, 1), (14071, 1), (69677, 1), (59087715390938998409, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_14071, prime_ninetyEightCR_69677, prime_ninetyEightCR_59087715390938998409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436807 : Nat.totient 115862154642076597416113436807 = 75153830038103738864506012992 := by
  rw [← show ((([(3, 1), (37, 1), (1043803194973663039784805737, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_37, prime_ninetyEightCR_1043803194973663039784805737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436808 : Nat.totient 115862154642076597416113436808 = 57656518826851105552587430080 := by
  rw [← show ((([(2, 3), (211, 1), (15903637, 1), (4315913221926637343, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_211, prime_ninetyEightCR_15903637, prime_ninetyEightCR_4315913221926637343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436809 : Nat.totient 115862154642076597416113436809 = 103602522779800236139594726800 := by
  rw [← show ((([(11, 1), (61, 1), (172670871299667060232657879, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_11, prime_ninetyEightCR_61, prime_ninetyEightCR_172670871299667060232657879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436810 : Nat.totient 115862154642076597416113436810 = 26480260455677595639160704000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19087, 1), (23431, 1), (507195631, 1), (810768841, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_7, prime_ninetyEightCR_19087, prime_ninetyEightCR_23431, prime_ninetyEightCR_507195631, prime_ninetyEightCR_810768841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436811 : Nat.totient 115862154642076597416113436811 = 115843672881606706049818029792 := by
  rw [← show ((([(6269, 1), (420475296523, 1), (43954449511253, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_6269, prime_ninetyEightCR_420475296523, prime_ninetyEightCR_43954449511253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436812 : Nat.totient 115862154642076597416113436812 = 57931077321038298708056718404 := by
  rw [← show ((([(2, 2), (28965538660519149354028359203, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_28965538660519149354028359203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436813 : Nat.totient 115862154642076597416113436813 = 75880972128940148729269267200 := by
  rw [← show ((([(3, 1), (71, 1), (311, 1), (4007, 1), (8677, 1), (50305175479592069, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_71, prime_ninetyEightCR_311, prime_ninetyEightCR_4007, prime_ninetyEightCR_8677, prime_ninetyEightCR_50305175479592069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436814 : Nat.totient 115862154642076597416113436814 = 55412238508593701318164416000 := by
  rw [← show ((([(2, 1), (23, 1), (576701, 1), (235607089, 1), (18537224560181, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_23, prime_ninetyEightCR_576701, prime_ninetyEightCR_235607089, prime_ninetyEightCR_18537224560181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436815 : Nat.totient 115862154642076597416113436815 = 89459917734302385404735099520 := by
  rw [← show ((([(5, 1), (29, 1), (2683, 1), (353819, 1), (841728001621930711, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_29, prime_ninetyEightCR_2683, prime_ninetyEightCR_353819, prime_ninetyEightCR_841728001621930711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436816 : Nat.totient 115862154642076597416113436816 = 35649893736023568435727211136 := by
  rw [← show ((([(2, 4), (3, 1), (13, 1), (185676529875122752269412559, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_13, prime_ninetyEightCR_185676529875122752269412559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436817 : Nat.totient 115862154642076597416113436817 = 99310418251721515350434658120 := by
  rw [← show ((([(7, 2), (7689202643, 1), (307513519670110331, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7, prime_ninetyEightCR_7689202643, prime_ninetyEightCR_307513519670110331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436818 : Nat.totient 115862154642076597416113436818 = 57368890017872279549615203200 := by
  rw [← show ((([(2, 1), (131, 1), (487, 1), (30091, 1), (4849049, 1), (6223262995783, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_131, prime_ninetyEightCR_487, prime_ninetyEightCR_30091, prime_ninetyEightCR_4849049, prime_ninetyEightCR_6223262995783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436819 : Nat.totient 115862154642076597416113436819 = 72599776079479781060097691200 := by
  rw [← show ((([(3, 2), (19, 1), (127, 1), (550651, 1), (9688696171250312357, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_19, prime_ninetyEightCR_127, prime_ninetyEightCR_550651, prime_ninetyEightCR_9688696171250312357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436820 : Nat.totient 115862154642076597416113436820 = 39653357738464717832252725760 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (17, 1), (30979185733175560806447443, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_11, prime_ninetyEightCR_17, prime_ninetyEightCR_30979185733175560806447443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436821 : Nat.totient 115862154642076597416113436821 = 115862139795893108858948515500 := by
  rw [← show ((([(7804171, 1), (14846183488557157117151, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7804171, prime_ninetyEightCR_14846183488557157117151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436822 : Nat.totient 115862154642076597416113436822 = 38620718207684832986211538632 := by
  rw [← show ((([(2, 1), (3, 1), (6090923939, 1), (3170349736822212883, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_6090923939, prime_ninetyEightCR_3170349736822212883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436823 : Nat.totient 115862154642076597416113436823 = 115861402783624471252196271480 := by
  rw [← show ((([(154127, 1), (914216059, 1), (822269212534811, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_154127, prime_ninetyEightCR_914216059, prime_ninetyEightCR_822269212534811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436824 : Nat.totient 115862154642076597416113436824 = 49432052459929137113036390400 := by
  rw [← show ((([(2, 3), (7, 1), (257, 1), (1741, 1), (32191, 1), (143643907672236887, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_7, prime_ninetyEightCR_257, prime_ninetyEightCR_1741, prime_ninetyEightCR_32191, prime_ninetyEightCR_143643907672236887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436825 : Nat.totient 115862154642076597416113436825 = 61448555129968083059876206080 := by
  rw [← show ((([(3, 1), (5, 2), (229, 1), (823, 1), (8196812856155301983273, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_229, prime_ninetyEightCR_823, prime_ninetyEightCR_8196812856155301983273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436826 : Nat.totient 115862154642076597416113436826 = 55998693709495437769124256000 := by
  rw [← show ((([(2, 1), (31, 1), (881, 1), (13029823, 1), (162792910026797821, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_31, prime_ninetyEightCR_881, prime_ninetyEightCR_13029823, prime_ninetyEightCR_162792910026797821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436827 : Nat.totient 115862154642076597416113436827 = 115860628754696712038633594880 := by
  rw [← show ((([(75931, 1), (1525887379885377479766017, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_75931, prime_ninetyEightCR_1525887379885377479766017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436828 : Nat.totient 115862154642076597416113436828 = 38616701091187016123863447680 := by
  rw [← show ((([(2, 2), (3, 3), (9791, 1), (531833, 1), (206022908027055347, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_9791, prime_ninetyEightCR_531833, prime_ninetyEightCR_206022908027055347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436829 : Nat.totient 115862154642076597416113436829 = 106949681208070705307181633984 := by
  rw [← show ((([(13, 1), (8912473434005892108931802833, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_13, prime_ninetyEightCR_8912473434005892108931802833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436830 : Nat.totient 115862154642076597416113436830 = 46128723010476686870623543296 := by
  rw [← show ((([(2, 1), (5, 1), (373, 1), (503, 1), (119106470929, 1), (518476918033, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_373, prime_ninetyEightCR_503, prime_ninetyEightCR_119106470929, prime_ninetyEightCR_518476918033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436831 : Nat.totient 115862154642076597416113436831 = 59544146459752332988489044480 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (107, 1), (733, 1), (440203, 1), (14527432641899557, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_7, prime_ninetyEightCR_11, prime_ninetyEightCR_107, prime_ninetyEightCR_733, prime_ninetyEightCR_440203, prime_ninetyEightCR_14527432641899557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436832 : Nat.totient 115862154642076597416113436832 = 57911217500613103251871530240 := by
  rw [← show ((([(2, 5), (2917, 1), (8957826043, 1), (138564688188371, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_2917, prime_ninetyEightCR_8957826043, prime_ninetyEightCR_138564688188371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436833 : Nat.totient 115862154642076597416113436833 = 115664984890473425807232000000 := by
  rw [← show ((([(1201, 1), (2131, 1), (3001, 1), (14813, 1), (28466947, 1), (35773813, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_1201, prime_ninetyEightCR_2131, prime_ninetyEightCR_3001, prime_ninetyEightCR_14813, prime_ninetyEightCR_28466947, prime_ninetyEightCR_35773813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436834 : Nat.totient 115862154642076597416113436834 = 38389431630776035713728447808 := by
  rw [← show ((([(2, 1), (3, 1), (167, 1), (1669219, 1), (21338477, 1), (3246363453259, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_167, prime_ninetyEightCR_1669219, prime_ninetyEightCR_21338477, prime_ninetyEightCR_3246363453259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436835 : Nat.totient 115862154642076597416113436835 = 92689723713661277932890749464 := by
  rw [← show ((([(5, 1), (23172430928415319483222687367, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_23172430928415319483222687367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436836 : Nat.totient 115862154642076597416113436836 = 57893238596558191451471451360 := by
  rw [← show ((([(2, 2), (1531, 1), (8991161887, 1), (2104217370164597, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_1531, prime_ninetyEightCR_8991161887, prime_ninetyEightCR_2104217370164597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436837 : Nat.totient 115862154642076597416113436837 = 69536724069586342363944247296 := by
  rw [← show ((([(3, 2), (17, 1), (23, 1), (217979, 1), (15280393, 1), (9884919885209, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_17, prime_ninetyEightCR_23, prime_ninetyEightCR_217979, prime_ninetyEightCR_15280393, prime_ninetyEightCR_9884919885209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436838 : Nat.totient 115862154642076597416113436838 = 45892498835221258267248399360 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (41, 1), (24133, 1), (2851799, 1), (154363949592869, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_7, prime_ninetyEightCR_19, prime_ninetyEightCR_41, prime_ninetyEightCR_24133, prime_ninetyEightCR_2851799, prime_ninetyEightCR_154363949592869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436839 : Nat.totient 115862154642076597416113436839 = 115862154640840910335901011824 := by
  rw [← show ((([(93763352623, 1), (1235686986449072393, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_93763352623, prime_ninetyEightCR_1235686986449072393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436840 : Nat.totient 115862154642076597416113436840 = 30239134495883215707478063104 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (47, 1), (479623, 1), (9753209, 1), (4391521008283, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_47, prime_ninetyEightCR_479623, prime_ninetyEightCR_9753209, prime_ninetyEightCR_4391521008283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436841 : Nat.totient 115862154642076597416113436841 = 115862154618855363208952130900 := by
  rw [← show ((([(4989491671, 1), (23221234202171814271, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_4989491671, prime_ninetyEightCR_23221234202171814271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436842 : Nat.totient 115862154642076597416113436842 = 47460323376240950157716160000 := by
  rw [← show ((([(2, 1), (11, 1), (13, 1), (43, 1), (2099, 1), (673318771, 1), (6666132647401, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_11, prime_ninetyEightCR_13, prime_ninetyEightCR_43, prime_ninetyEightCR_2099, prime_ninetyEightCR_673318771, prime_ninetyEightCR_6666132647401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436843 : Nat.totient 115862154642076597416113436843 = 75784050835068969379093065504 := by
  rw [← show ((([(3, 1), (53, 1), (728692796491047782491279477, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_53, prime_ninetyEightCR_728692796491047782491279477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436844 : Nat.totient 115862154642076597416113436844 = 54177592334583559793326018560 := by
  rw [← show ((([(2, 2), (29, 1), (37, 1), (223, 1), (526069, 1), (230109375452914961, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_29, prime_ninetyEightCR_37, prime_ninetyEightCR_223, prime_ninetyEightCR_526069, prime_ninetyEightCR_230109375452914961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436845 : Nat.totient 115862154642076597416113436845 = 79040983933879556550034993920 := by
  rw [← show ((([(5, 1), (7, 1), (197, 1), (19471, 1), (8769488339, 1), (98411265919, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_7, prime_ninetyEightCR_197, prime_ninetyEightCR_19471, prime_ninetyEightCR_8769488339, prime_ninetyEightCR_98411265919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436846 : Nat.totient 115862154642076597416113436846 = 38459113256160855331419643920 := by
  rw [← show ((([(2, 1), (3, 2), (239, 1), (3206363, 1), (8399598092844371971, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_239, prime_ninetyEightCR_3206363, prime_ninetyEightCR_8399598092844371971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436847 : Nat.totient 115862154642076597416113436847 = 115862154639240577255661436376 := by
  rw [← show ((([(40853784443, 1), (2836020119598216029, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_40853784443, prime_ninetyEightCR_2836020119598216029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436848 : Nat.totient 115862154642076597416113436848 = 57928548431133628341778080000 := by
  rw [← show ((([(2, 4), (27061, 1), (149251, 1), (1792918411691793173, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_27061, prime_ninetyEightCR_149251, prime_ninetyEightCR_1792918411691793173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436849 : Nat.totient 115862154642076597416113436849 = 77241436428051064944075624564 := by
  rw [← show ((([(3, 1), (38620718214025532472037812283, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_38620718214025532472037812283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436850 : Nat.totient 115862154642076597416113436850 = 46309368586690107862996032000 := by
  rw [← show ((([(2, 1), (5, 2), (2399, 1), (2939, 1), (130651, 1), (797833, 1), (3152949599, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_2399, prime_ninetyEightCR_2939, prime_ninetyEightCR_130651, prime_ninetyEightCR_797833, prime_ninetyEightCR_3152949599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436851 : Nat.totient 115862154642076597416113436851 = 115862124446183631063185592432 := by
  rw [← show ((([(3837017, 1), (30195892966352924007403, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3837017, prime_ninetyEightCR_30195892966352924007403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436852 : Nat.totient 115862154642076597416113436852 = 33080333239454322779271336960 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (2467, 1), (4729, 1), (13523, 1), (119291, 1), (73289730347, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_7, prime_ninetyEightCR_2467, prime_ninetyEightCR_4729, prime_ninetyEightCR_13523, prime_ninetyEightCR_119291, prime_ninetyEightCR_73289730347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436853 : Nat.totient 115862154642076597416113436853 = 103757153410814863357713524880 := by
  rw [← show ((([(11, 1), (67, 1), (157207808198204338420778069, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_11, prime_ninetyEightCR_67, prime_ninetyEightCR_157207808198204338420778069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436854 : Nat.totient 115862154642076597416113436854 = 54522851209811964974809013760 := by
  rw [← show ((([(2, 1), (17, 1), (105733, 1), (5305362347, 1), (6074871250381, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_17, prime_ninetyEightCR_105733, prime_ninetyEightCR_5305362347, prime_ninetyEightCR_6074871250381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436855 : Nat.totient 115862154642076597416113436855 = 55363267712065693262338280448 := by
  rw [← show ((([(3, 4), (5, 1), (13, 1), (59, 1), (79, 1), (22077819629, 1), (213849353303, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_13, prime_ninetyEightCR_59, prime_ninetyEightCR_79, prime_ninetyEightCR_22077819629, prime_ninetyEightCR_213849353303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436856 : Nat.totient 115862154642076597416113436856 = 57930384116227023593278643200 := by
  rw [← show ((([(2, 3), (83921, 1), (19976591, 1), (8638922648436137, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_83921, prime_ninetyEightCR_19976591, prime_ninetyEightCR_8638922648436137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436857 : Nat.totient 115862154642076597416113436857 = 106214858861987205990239400000 := by
  rw [← show ((([(19, 1), (31, 1), (13451, 1), (173651, 1), (84215967930088013, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_19, prime_ninetyEightCR_31, prime_ninetyEightCR_13451, prime_ninetyEightCR_173651, prime_ninetyEightCR_84215967930088013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436858 : Nat.totient 115862154642076597416113436858 = 38584515330640733981337578880 := by
  rw [← show ((([(2, 1), (3, 1), (1069, 1), (514531, 1), (35107596586493078537, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_1069, prime_ninetyEightCR_514531, prime_ninetyEightCR_35107596586493078537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436859 : Nat.totient 115862154642076597416113436859 = 98286599519640824906747185920 := by
  rw [← show ((([(7, 1), (97, 1), (170636457499376432129769421, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7, prime_ninetyEightCR_97, prime_ninetyEightCR_170636457499376432129769421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436860 : Nat.totient 115862154642076597416113436860 = 43937568146406156225593891840 := by
  rw [← show ((([(2, 2), (5, 1), (23, 1), (113, 1), (41999318267, 1), (53071710418271, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_23, prime_ninetyEightCR_113, prime_ninetyEightCR_41999318267, prime_ninetyEightCR_53071710418271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436861 : Nat.totient 115862154642076597416113436861 = 77241436427653576177714344480 := by
  rw [← show ((([(3, 1), (194323760791, 1), (198744188856879257, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_194323760791, prime_ninetyEightCR_198744188856879257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436862 : Nat.totient 115862154642076597416113436862 = 57623300667734203400002228224 := by
  rw [← show ((([(2, 1), (263, 1), (673, 1), (32839, 1), (1305860447, 1), (7632276593, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_263, prime_ninetyEightCR_673, prime_ninetyEightCR_32839, prime_ninetyEightCR_1305860447, prime_ninetyEightCR_7632276593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436863 : Nat.totient 115862154642076597416113436863 = 115845510172224266343362946720 := by
  rw [← show ((([(6961, 1), (16644469852331072750483183, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_6961, prime_ninetyEightCR_16644469852331072750483183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436864 : Nat.totient 115862154642076597416113436864 = 35109743830932302247307100160 := by
  rw [← show ((([(2, 6), (3, 2), (11, 1), (18286324911943907420472449, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_11, prime_ninetyEightCR_18286324911943907420472449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436865 : Nat.totient 115862154642076597416113436865 = 92689723713656629649585018880 := by
  rw [← show ((([(5, 1), (20295080724493, 1), (1141775745708161, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_20295080724493, prime_ninetyEightCR_1141775745708161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436866 : Nat.totient 115862154642076597416113436866 = 49655209132318541749762901472 := by
  rw [← show ((([(2, 1), (7, 2), (1182266884102822422613402417, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_7, prime_ninetyEightCR_1182266884102822422613402417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436867 : Nat.totient 115862154642076597416113436867 = 76310625967912033454398694112 := by
  rw [← show ((([(3, 1), (83, 1), (400069, 1), (1163074014733227568607, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_83, prime_ninetyEightCR_400069, prime_ninetyEightCR_1163074014733227568607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436868 : Nat.totient 115862154642076597416113436868 = 53115564138650884038584346624 := by
  rw [← show ((([(2, 2), (13, 1), (149, 1), (137993, 1), (108366471390484062937, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_13, prime_ninetyEightCR_149, prime_ninetyEightCR_137993, prime_ninetyEightCR_108366471390484062937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436869 : Nat.totient 115862154642076597416113436869 = 115862152632344989737917191680 := by
  rw [← show ((([(57650561, 1), (2009731607678138594629, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_57650561, prime_ninetyEightCR_2009731607678138594629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436870 : Nat.totient 115862154642076597416113436870 = 30390073348557656361919420800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (61, 1), (165463059059, 1), (382639201583371, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_61, prime_ninetyEightCR_165463059059, prime_ninetyEightCR_382639201583371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436871 : Nat.totient 115862154642076597416113436871 = 108443227482737337197758464000 := by
  rw [← show ((([(17, 1), (181, 1), (104473, 1), (758270641, 1), (475319681411, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_17, prime_ninetyEightCR_181, prime_ninetyEightCR_104473, prime_ninetyEightCR_758270641, prime_ninetyEightCR_475319681411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436872 : Nat.totient 115862154642076597416113436872 = 57920242981472675132965511040 := by
  rw [← show ((([(2, 3), (5347, 1), (2271588811, 1), (1192371834135577, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5347, prime_ninetyEightCR_2271588811, prime_ninetyEightCR_1192371834135577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436873 : Nat.totient 115862154642076597416113436873 = 63923925140187605467484428800 := by
  rw [← show ((([(3, 2), (7, 1), (29, 1), (3244277, 1), (25118851, 1), (778189480637, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_7, prime_ninetyEightCR_29, prime_ninetyEightCR_3244277, prime_ninetyEightCR_25118851, prime_ninetyEightCR_778189480637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436874 : Nat.totient 115862154642076597416113436874 = 57005543638318141331205414912 := by
  rw [← show ((([(2, 1), (73, 1), (433, 1), (13864573297, 1), (132188702701469, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_73, prime_ninetyEightCR_433, prime_ninetyEightCR_13864573297, prime_ninetyEightCR_132188702701469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436875 : Nat.totient 115862154642076597416113436875 = 84263385189161850106716080000 := by
  rw [← show ((([(5, 4), (11, 1), (16601685197, 1), (1015118455678997, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_11, prime_ninetyEightCR_16601685197, prime_ninetyEightCR_1015118455678997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436876 : Nat.totient 115862154642076597416113436876 = 35818759534592780863481548800 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (89, 1), (101, 1), (1126846447, 1), (50168444249449, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_19, prime_ninetyEightCR_89, prime_ninetyEightCR_101, prime_ninetyEightCR_1126846447, prime_ninetyEightCR_50168444249449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436877 : Nat.totient 115862154642076597416113436877 = 115858182192261446121797755824 := by
  rw [← show ((([(29167, 1), (1476219119, 1), (2690909012712749, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_29167, prime_ninetyEightCR_1476219119, prime_ninetyEightCR_2690909012712749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436878 : Nat.totient 115862154642076597416113436878 = 57931077320446181215147411320 := by
  rw [← show ((([(2, 1), (97837148179, 1), (592117395072158941, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_97837148179, prime_ninetyEightCR_592117395072158941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436879 : Nat.totient 115862154642076597416113436879 = 75357429368481786355818432000 := by
  rw [← show ((([(3, 1), (41, 1), (1131763, 1), (25106231, 1), (33151217064041, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_41, prime_ninetyEightCR_1131763, prime_ninetyEightCR_25106231, prime_ninetyEightCR_33151217064041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436880 : Nat.totient 115862154642076597416113436880 = 39724167305854833399810321024 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (206896704717993923957345423, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_7, prime_ninetyEightCR_206896704717993923957345423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436881 : Nat.totient 115862154642076597416113436881 = 104059149283528253812392940800 := by
  rw [← show ((([(13, 1), (37, 1), (240877660378537624565724401, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_13, prime_ninetyEightCR_37, prime_ninetyEightCR_240877660378537624565724401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436882 : Nat.totient 115862154642076597416113436882 = 38619052737943889109350612160 := by
  rw [← show ((([(2, 1), (3, 3), (23189, 1), (184282792891, 1), (502089379117, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_23189, prime_ninetyEightCR_184282792891, prime_ninetyEightCR_502089379117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436883 : Nat.totient 115862154642076597416113436883 = 110824669657638484484978070040 := by
  rw [← show ((([(23, 1), (5037484984438112931135366821, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_23, prime_ninetyEightCR_5037484984438112931135366821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436884 : Nat.totient 115862154642076597416113436884 = 57115137036708993930161241600 := by
  rw [← show ((([(2, 2), (71, 1), (5984453, 1), (779604977, 1), (87442828471, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_71, prime_ninetyEightCR_5984453, prime_ninetyEightCR_779604977, prime_ninetyEightCR_87442828471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436885 : Nat.totient 115862154642076597416113436885 = 60351526330708372140949198848 := by
  rw [← show ((([(3, 1), (5, 1), (43, 1), (13219, 1), (8656283, 1), (1569827154108769, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_43, prime_ninetyEightCR_13219, prime_ninetyEightCR_8656283, prime_ninetyEightCR_1569827154108769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436886 : Nat.totient 115862154642076597416113436886 = 52664615746398453370960653120 := by
  rw [← show ((([(2, 1), (11, 1), (5266461574639845337096065313, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_11, prime_ninetyEightCR_5266461574639845337096065313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436887 : Nat.totient 115862154642076597416113436887 = 97192733756518759836714940800 := by
  rw [← show ((([(7, 1), (47, 1), (20717, 1), (18653309, 1), (911303319187351, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7, prime_ninetyEightCR_47, prime_ninetyEightCR_20717, prime_ninetyEightCR_18653309, prime_ninetyEightCR_911303319187351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436888 : Nat.totient 115862154642076597416113436888 = 35136255853575176459958558720 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (31, 1), (877, 1), (38259222349, 1), (273013430447, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_17, prime_ninetyEightCR_31, prime_ninetyEightCR_877, prime_ninetyEightCR_38259222349, prime_ninetyEightCR_273013430447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436889 : Nat.totient 115862154642076597416113436889 = 115819131002874559475014917936 := by
  rw [← show ((([(2693, 1), (616735279, 1), (69759997316650187, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2693, prime_ninetyEightCR_616735279, prime_ninetyEightCR_69759997316650187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436890 : Nat.totient 115862154642076597416113436890 = 46344860897975309846157396480 := by
  rw [← show ((([(2, 1), (5, 1), (48333529, 1), (239713832280023661041, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_5, prime_ninetyEightCR_48333529, prime_ninetyEightCR_239713832280023661041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436891 : Nat.totient 115862154642076597416113436891 = 76976068883076553628932300800 := by
  rw [← show ((([(3, 2), (421, 1), (941, 1), (11391427, 1), (2852654929465217, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_421, prime_ninetyEightCR_941, prime_ninetyEightCR_11391427, prime_ninetyEightCR_2852654929465217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436892 : Nat.totient 115862154642076597416113436892 = 57929243072318384884204961120 := by
  rw [← show ((([(2, 2), (31583, 1), (917124359956911925847081, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_31583, prime_ninetyEightCR_917124359956911925847081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436893 : Nat.totient 115862154642076597416113436893 = 115484753486890680160686356988 := by
  rw [← show ((([(307, 1), (377401155185917255427079599, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_307, prime_ninetyEightCR_377401155185917255427079599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436894 : Nat.totient 115862154642076597416113436894 = 30557051773734487230623323872 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13, 1), (212201748428711716879328639, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_7, prime_ninetyEightCR_13, prime_ninetyEightCR_212201748428711716879328639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436895 : Nat.totient 115862154642076597416113436895 = 87808962140742842850343127040 := by
  rw [← show ((([(5, 1), (19, 1), (66541, 1), (84947, 1), (52275089, 1), (4127488247, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_5, prime_ninetyEightCR_19, prime_ninetyEightCR_66541, prime_ninetyEightCR_84947, prime_ninetyEightCR_52275089, prime_ninetyEightCR_4127488247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436896 : Nat.totient 115862154642076597416113436896 = 56838038126301727034319798400 := by
  rw [← show ((([(2, 5), (53, 1), (68314949671035729608557451, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_53, prime_ninetyEightCR_68314949671035729608557451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436897 : Nat.totient 115862154642076597416113436897 = 70185693154809800165807439360 := by
  rw [← show ((([(3, 1), (11, 1), (2393, 1), (15773, 1), (89673187, 1), (1037308780063, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_11, prime_ninetyEightCR_2393, prime_ninetyEightCR_15773, prime_ninetyEightCR_89673187, prime_ninetyEightCR_1037308780063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436898 : Nat.totient 115862154642076597416113436898 = 57562088930409452421814451280 := by
  rw [← show ((([(2, 1), (157, 1), (90365531, 1), (4083279869590835647, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_157, prime_ninetyEightCR_90365531, prime_ninetyEightCR_4083279869590835647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436899 : Nat.totient 115862154642076597416113436899 = 115424517783288351394006425600 := by
  rw [← show ((([(317, 1), (1601, 1), (148223729, 1), (1540186354894543, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_317, prime_ninetyEightCR_1601, prime_ninetyEightCR_148223729, prime_ninetyEightCR_1540186354894543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436900 : Nat.totient 115862154642076597416113436900 = 30596255285309171954496000000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (103, 1), (92921, 1), (1315007, 1), (10228687885001, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_3, prime_ninetyEightCR_5, prime_ninetyEightCR_103, prime_ninetyEightCR_92921, prime_ninetyEightCR_1315007, prime_ninetyEightCR_10228687885001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436901 : Nat.totient 115862154642076597416113436901 = 99310418241925744849780992480 := by
  rw [← show ((([(7, 1), (4372724123, 1), (3785223103918077641, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_7, prime_ninetyEightCR_4372724123, prime_ninetyEightCR_3785223103918077641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436902 : Nat.totient 115862154642076597416113436902 = 55933434184446095355469722240 := by
  rw [← show ((([(2, 1), (29, 1), (2827679, 1), (706453368963688017361, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436902 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_2, prime_ninetyEightCR_29, prime_ninetyEightCR_2827679, prime_ninetyEightCR_706453368963688017361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyEightCR_115862154642076597416113436903 : Nat.totient 115862154642076597416113436903 = 77231078182509281839536629760 := by
  rw [← show ((([(3, 1), (7457, 1), (1348510395173, 1), (3840624996841, 1)] : List FactorBlock).map factorBlockValue).prod) = 115862154642076597416113436903 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyEightCR_3, prime_ninetyEightCR_7457, prime_ninetyEightCR_1348510395173, prime_ninetyEightCR_3840624996841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyEightCR : certifiedKill 3 115862154642076597416113436799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyEightCR_115862154642076597416113436800, phi_ninetyEightCR_115862154642076597416113436801, phi_ninetyEightCR_115862154642076597416113436802,
    phi_ninetyEightCR_115862154642076597416113436803, phi_ninetyEightCR_115862154642076597416113436804, phi_ninetyEightCR_115862154642076597416113436805,
    phi_ninetyEightCR_115862154642076597416113436806, phi_ninetyEightCR_115862154642076597416113436807, phi_ninetyEightCR_115862154642076597416113436808,
    phi_ninetyEightCR_115862154642076597416113436809, phi_ninetyEightCR_115862154642076597416113436810, phi_ninetyEightCR_115862154642076597416113436811,
    phi_ninetyEightCR_115862154642076597416113436812, phi_ninetyEightCR_115862154642076597416113436813, phi_ninetyEightCR_115862154642076597416113436814,
    phi_ninetyEightCR_115862154642076597416113436815, phi_ninetyEightCR_115862154642076597416113436816, phi_ninetyEightCR_115862154642076597416113436817,
    phi_ninetyEightCR_115862154642076597416113436818, phi_ninetyEightCR_115862154642076597416113436819, phi_ninetyEightCR_115862154642076597416113436820,
    phi_ninetyEightCR_115862154642076597416113436821, phi_ninetyEightCR_115862154642076597416113436822, phi_ninetyEightCR_115862154642076597416113436823,
    phi_ninetyEightCR_115862154642076597416113436824, phi_ninetyEightCR_115862154642076597416113436825, phi_ninetyEightCR_115862154642076597416113436826,
    phi_ninetyEightCR_115862154642076597416113436827, phi_ninetyEightCR_115862154642076597416113436828, phi_ninetyEightCR_115862154642076597416113436829,
    phi_ninetyEightCR_115862154642076597416113436830, phi_ninetyEightCR_115862154642076597416113436831, phi_ninetyEightCR_115862154642076597416113436832,
    phi_ninetyEightCR_115862154642076597416113436833, phi_ninetyEightCR_115862154642076597416113436834, phi_ninetyEightCR_115862154642076597416113436835,
    phi_ninetyEightCR_115862154642076597416113436836, phi_ninetyEightCR_115862154642076597416113436837, phi_ninetyEightCR_115862154642076597416113436838,
    phi_ninetyEightCR_115862154642076597416113436839, phi_ninetyEightCR_115862154642076597416113436840, phi_ninetyEightCR_115862154642076597416113436841,
    phi_ninetyEightCR_115862154642076597416113436842, phi_ninetyEightCR_115862154642076597416113436843, phi_ninetyEightCR_115862154642076597416113436844,
    phi_ninetyEightCR_115862154642076597416113436845, phi_ninetyEightCR_115862154642076597416113436846, phi_ninetyEightCR_115862154642076597416113436847,
    phi_ninetyEightCR_115862154642076597416113436848, phi_ninetyEightCR_115862154642076597416113436849, phi_ninetyEightCR_115862154642076597416113436850,
    phi_ninetyEightCR_115862154642076597416113436851, phi_ninetyEightCR_115862154642076597416113436852, phi_ninetyEightCR_115862154642076597416113436853,
    phi_ninetyEightCR_115862154642076597416113436854, phi_ninetyEightCR_115862154642076597416113436855, phi_ninetyEightCR_115862154642076597416113436856,
    phi_ninetyEightCR_115862154642076597416113436857, phi_ninetyEightCR_115862154642076597416113436858, phi_ninetyEightCR_115862154642076597416113436859,
    phi_ninetyEightCR_115862154642076597416113436860, phi_ninetyEightCR_115862154642076597416113436861, phi_ninetyEightCR_115862154642076597416113436862,
    phi_ninetyEightCR_115862154642076597416113436863, phi_ninetyEightCR_115862154642076597416113436864, phi_ninetyEightCR_115862154642076597416113436865,
    phi_ninetyEightCR_115862154642076597416113436866, phi_ninetyEightCR_115862154642076597416113436867, phi_ninetyEightCR_115862154642076597416113436868,
    phi_ninetyEightCR_115862154642076597416113436869, phi_ninetyEightCR_115862154642076597416113436870, phi_ninetyEightCR_115862154642076597416113436871,
    phi_ninetyEightCR_115862154642076597416113436872, phi_ninetyEightCR_115862154642076597416113436873, phi_ninetyEightCR_115862154642076597416113436874,
    phi_ninetyEightCR_115862154642076597416113436875, phi_ninetyEightCR_115862154642076597416113436876, phi_ninetyEightCR_115862154642076597416113436877,
    phi_ninetyEightCR_115862154642076597416113436878, phi_ninetyEightCR_115862154642076597416113436879, phi_ninetyEightCR_115862154642076597416113436880,
    phi_ninetyEightCR_115862154642076597416113436881, phi_ninetyEightCR_115862154642076597416113436882, phi_ninetyEightCR_115862154642076597416113436883,
    phi_ninetyEightCR_115862154642076597416113436884, phi_ninetyEightCR_115862154642076597416113436885, phi_ninetyEightCR_115862154642076597416113436886,
    phi_ninetyEightCR_115862154642076597416113436887, phi_ninetyEightCR_115862154642076597416113436888, phi_ninetyEightCR_115862154642076597416113436889,
    phi_ninetyEightCR_115862154642076597416113436890, phi_ninetyEightCR_115862154642076597416113436891, phi_ninetyEightCR_115862154642076597416113436892,
    phi_ninetyEightCR_115862154642076597416113436893, phi_ninetyEightCR_115862154642076597416113436894, phi_ninetyEightCR_115862154642076597416113436895,
    phi_ninetyEightCR_115862154642076597416113436896, phi_ninetyEightCR_115862154642076597416113436897, phi_ninetyEightCR_115862154642076597416113436898,
    phi_ninetyEightCR_115862154642076597416113436899, phi_ninetyEightCR_115862154642076597416113436900, phi_ninetyEightCR_115862154642076597416113436901,
    phi_ninetyEightCR_115862154642076597416113436902, phi_ninetyEightCR_115862154642076597416113436903]

end TotientTailPeriodKiller
end Erdos249257
