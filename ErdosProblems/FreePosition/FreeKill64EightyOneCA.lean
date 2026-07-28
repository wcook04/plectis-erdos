import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyOneCAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyOneCAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyOneCAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyOneCAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyOneCAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyOneCAFastPow a n * eightyOneCAFastPow a n * a else eightyOneCAFastPow a n * eightyOneCAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyOneCA_2 : Nat.Prime 2 := by norm_num
private theorem prime_eightyOneCA_3 : Nat.Prime 3 := by norm_num
private theorem prime_eightyOneCA_5 : Nat.Prime 5 := by norm_num
private theorem prime_eightyOneCA_7 : Nat.Prime 7 := by norm_num
private theorem prime_eightyOneCA_11 : Nat.Prime 11 := by norm_num
private theorem prime_eightyOneCA_13 : Nat.Prime 13 := by norm_num
private theorem prime_eightyOneCA_17 : Nat.Prime 17 := by norm_num
private theorem prime_eightyOneCA_19 : Nat.Prime 19 := by norm_num
private theorem prime_eightyOneCA_23 : Nat.Prime 23 := by norm_num
private theorem prime_eightyOneCA_29 : Nat.Prime 29 := by norm_num
private theorem prime_eightyOneCA_31 : Nat.Prime 31 := by norm_num
private theorem prime_eightyOneCA_37 : Nat.Prime 37 := by norm_num
private theorem prime_eightyOneCA_41 : Nat.Prime 41 := by norm_num
private theorem prime_eightyOneCA_43 : Nat.Prime 43 := by norm_num
private theorem prime_eightyOneCA_47 : Nat.Prime 47 := by norm_num
private theorem prime_eightyOneCA_53 : Nat.Prime 53 := by norm_num
private theorem prime_eightyOneCA_59 : Nat.Prime 59 := by norm_num
private theorem prime_eightyOneCA_61 : Nat.Prime 61 := by norm_num
private theorem prime_eightyOneCA_67 : Nat.Prime 67 := by norm_num
private theorem prime_eightyOneCA_71 : Nat.Prime 71 := by norm_num
private theorem prime_eightyOneCA_73 : Nat.Prime 73 := by norm_num
private theorem prime_eightyOneCA_79 : Nat.Prime 79 := by norm_num
private theorem prime_eightyOneCA_83 : Nat.Prime 83 := by norm_num
private theorem prime_eightyOneCA_89 : Nat.Prime 89 := by norm_num
private theorem prime_eightyOneCA_97 : Nat.Prime 97 := by norm_num
private theorem prime_eightyOneCA_101 : Nat.Prime 101 := by norm_num
private theorem prime_eightyOneCA_103 : Nat.Prime 103 := by norm_num
private theorem prime_eightyOneCA_107 : Nat.Prime 107 := by norm_num
private theorem prime_eightyOneCA_109 : Nat.Prime 109 := by norm_num
private theorem prime_eightyOneCA_113 : Nat.Prime 113 := by norm_num
private theorem prime_eightyOneCA_127 : Nat.Prime 127 := by norm_num
private theorem prime_eightyOneCA_137 : Nat.Prime 137 := by norm_num
private theorem prime_eightyOneCA_139 : Nat.Prime 139 := by norm_num
private theorem prime_eightyOneCA_149 : Nat.Prime 149 := by norm_num
private theorem prime_eightyOneCA_151 : Nat.Prime 151 := by norm_num
private theorem prime_eightyOneCA_157 : Nat.Prime 157 := by norm_num
private theorem prime_eightyOneCA_163 : Nat.Prime 163 := by norm_num
private theorem prime_eightyOneCA_167 : Nat.Prime 167 := by norm_num
private theorem prime_eightyOneCA_173 : Nat.Prime 173 := by norm_num
private theorem prime_eightyOneCA_179 : Nat.Prime 179 := by norm_num
private theorem prime_eightyOneCA_181 : Nat.Prime 181 := by norm_num
private theorem prime_eightyOneCA_191 : Nat.Prime 191 := by norm_num
private theorem prime_eightyOneCA_193 : Nat.Prime 193 := by norm_num
private theorem prime_eightyOneCA_197 : Nat.Prime 197 := by norm_num
private theorem prime_eightyOneCA_211 : Nat.Prime 211 := by norm_num
private theorem prime_eightyOneCA_223 : Nat.Prime 223 := by norm_num
private theorem prime_eightyOneCA_227 : Nat.Prime 227 := by norm_num
private theorem prime_eightyOneCA_229 : Nat.Prime 229 := by norm_num
private theorem prime_eightyOneCA_233 : Nat.Prime 233 := by norm_num
private theorem prime_eightyOneCA_239 : Nat.Prime 239 := by norm_num
private theorem prime_eightyOneCA_241 : Nat.Prime 241 := by norm_num
private theorem prime_eightyOneCA_251 : Nat.Prime 251 := by norm_num
private theorem prime_eightyOneCA_257 : Nat.Prime 257 := by norm_num
private theorem prime_eightyOneCA_263 : Nat.Prime 263 := by norm_num
private theorem prime_eightyOneCA_277 : Nat.Prime 277 := by norm_num
private theorem prime_eightyOneCA_281 : Nat.Prime 281 := by norm_num
private theorem prime_eightyOneCA_283 : Nat.Prime 283 := by norm_num
private theorem prime_eightyOneCA_293 : Nat.Prime 293 := by norm_num
private theorem prime_eightyOneCA_307 : Nat.Prime 307 := by norm_num
private theorem prime_eightyOneCA_311 : Nat.Prime 311 := by norm_num
private theorem prime_eightyOneCA_313 : Nat.Prime 313 := by norm_num
private theorem prime_eightyOneCA_331 : Nat.Prime 331 := by norm_num
private theorem prime_eightyOneCA_337 : Nat.Prime 337 := by norm_num
private theorem prime_eightyOneCA_353 : Nat.Prime 353 := by norm_num
private theorem prime_eightyOneCA_359 : Nat.Prime 359 := by norm_num
private theorem prime_eightyOneCA_367 : Nat.Prime 367 := by norm_num
private theorem prime_eightyOneCA_379 : Nat.Prime 379 := by norm_num
private theorem prime_eightyOneCA_389 : Nat.Prime 389 := by norm_num
private theorem prime_eightyOneCA_397 : Nat.Prime 397 := by norm_num
private theorem prime_eightyOneCA_401 : Nat.Prime 401 := by norm_num
private theorem prime_eightyOneCA_421 : Nat.Prime 421 := by norm_num
private theorem prime_eightyOneCA_431 : Nat.Prime 431 := by norm_num
private theorem prime_eightyOneCA_433 : Nat.Prime 433 := by norm_num
private theorem prime_eightyOneCA_439 : Nat.Prime 439 := by norm_num
private theorem prime_eightyOneCA_449 : Nat.Prime 449 := by norm_num
private theorem prime_eightyOneCA_463 : Nat.Prime 463 := by norm_num
private theorem prime_eightyOneCA_499 : Nat.Prime 499 := by norm_num
private theorem prime_eightyOneCA_509 : Nat.Prime 509 := by norm_num
private theorem prime_eightyOneCA_521 : Nat.Prime 521 := by norm_num
private theorem prime_eightyOneCA_569 : Nat.Prime 569 := by norm_num
private theorem prime_eightyOneCA_571 : Nat.Prime 571 := by norm_num
private theorem prime_eightyOneCA_593 : Nat.Prime 593 := by norm_num
private theorem prime_eightyOneCA_613 : Nat.Prime 613 := by norm_num
private theorem prime_eightyOneCA_617 : Nat.Prime 617 := by norm_num
private theorem prime_eightyOneCA_643 : Nat.Prime 643 := by norm_num
private theorem prime_eightyOneCA_691 : Nat.Prime 691 := by norm_num
private theorem prime_eightyOneCA_701 : Nat.Prime 701 := by norm_num
private theorem prime_eightyOneCA_709 : Nat.Prime 709 := by norm_num
private theorem prime_eightyOneCA_727 : Nat.Prime 727 := by norm_num
private theorem prime_eightyOneCA_751 : Nat.Prime 751 := by norm_num
private theorem prime_eightyOneCA_761 : Nat.Prime 761 := by norm_num
private theorem prime_eightyOneCA_769 : Nat.Prime 769 := by norm_num
private theorem prime_eightyOneCA_773 : Nat.Prime 773 := by norm_num
private theorem prime_eightyOneCA_787 : Nat.Prime 787 := by norm_num
private theorem prime_eightyOneCA_809 : Nat.Prime 809 := by norm_num
private theorem prime_eightyOneCA_811 : Nat.Prime 811 := by norm_num
private theorem prime_eightyOneCA_823 : Nat.Prime 823 := by norm_num
private theorem prime_eightyOneCA_829 : Nat.Prime 829 := by norm_num
private theorem prime_eightyOneCA_863 : Nat.Prime 863 := by norm_num
private theorem prime_eightyOneCA_947 : Nat.Prime 947 := by norm_num
private theorem prime_eightyOneCA_971 : Nat.Prime 971 := by norm_num
private theorem prime_eightyOneCA_977 : Nat.Prime 977 := by norm_num
private theorem prime_eightyOneCA_991 : Nat.Prime 991 := by norm_num
private theorem prime_eightyOneCA_997 : Nat.Prime 997 := by norm_num
private theorem prime_eightyOneCA_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_eightyOneCA_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_eightyOneCA_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_eightyOneCA_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_eightyOneCA_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_eightyOneCA_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_eightyOneCA_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_eightyOneCA_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_eightyOneCA_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_eightyOneCA_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_eightyOneCA_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_eightyOneCA_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_eightyOneCA_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_eightyOneCA_1549 : Nat.Prime 1549 := by norm_num
private theorem prime_eightyOneCA_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_eightyOneCA_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_eightyOneCA_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_eightyOneCA_1747 : Nat.Prime 1747 := by norm_num
private theorem prime_eightyOneCA_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_eightyOneCA_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_eightyOneCA_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_eightyOneCA_1877 : Nat.Prime 1877 := by norm_num
private theorem prime_eightyOneCA_1907 : Nat.Prime 1907 := by norm_num
private theorem prime_eightyOneCA_1913 : Nat.Prime 1913 := by norm_num
private theorem prime_eightyOneCA_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_eightyOneCA_2137 : Nat.Prime 2137 := by norm_num
private theorem prime_eightyOneCA_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_eightyOneCA_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_eightyOneCA_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_eightyOneCA_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_eightyOneCA_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_eightyOneCA_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_eightyOneCA_2459 : Nat.Prime 2459 := by norm_num
private theorem prime_eightyOneCA_2539 : Nat.Prime 2539 := by norm_num
private theorem prime_eightyOneCA_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_eightyOneCA_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_eightyOneCA_2617 : Nat.Prime 2617 := by norm_num
private theorem prime_eightyOneCA_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_eightyOneCA_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_eightyOneCA_2683 : Nat.Prime 2683 := by norm_num
private theorem prime_eightyOneCA_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_eightyOneCA_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_eightyOneCA_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_eightyOneCA_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_eightyOneCA_3011 : Nat.Prime 3011 := by norm_num
private theorem prime_eightyOneCA_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_eightyOneCA_3319 : Nat.Prime 3319 := by norm_num
private theorem prime_eightyOneCA_3389 : Nat.Prime 3389 := by norm_num
private theorem prime_eightyOneCA_3413 : Nat.Prime 3413 := by norm_num
private theorem prime_eightyOneCA_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_eightyOneCA_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_eightyOneCA_3517 : Nat.Prime 3517 := by norm_num
private theorem prime_eightyOneCA_3541 : Nat.Prime 3541 := by norm_num
private theorem prime_eightyOneCA_3547 : Nat.Prime 3547 := by norm_num
private theorem prime_eightyOneCA_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_eightyOneCA_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_eightyOneCA_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_eightyOneCA_3767 : Nat.Prime 3767 := by norm_num
private theorem prime_eightyOneCA_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_eightyOneCA_3889 : Nat.Prime 3889 := by norm_num
private theorem prime_eightyOneCA_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_eightyOneCA_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_eightyOneCA_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_eightyOneCA_4363 : Nat.Prime 4363 := by norm_num
private theorem prime_eightyOneCA_4391 : Nat.Prime 4391 := by norm_num
private theorem prime_eightyOneCA_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_eightyOneCA_5209 : Nat.Prime 5209 := by norm_num
private theorem prime_eightyOneCA_5303 : Nat.Prime 5303 := by norm_num
private theorem prime_eightyOneCA_5333 : Nat.Prime 5333 := by norm_num
private theorem prime_eightyOneCA_5393 : Nat.Prime 5393 := by norm_num
private theorem prime_eightyOneCA_5477 : Nat.Prime 5477 := by norm_num
private theorem prime_eightyOneCA_5483 : Nat.Prime 5483 := by norm_num
private theorem prime_eightyOneCA_5923 : Nat.Prime 5923 := by norm_num
private theorem prime_eightyOneCA_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_eightyOneCA_6163 : Nat.Prime 6163 := by norm_num
private theorem prime_eightyOneCA_6217 : Nat.Prime 6217 := by norm_num
private theorem prime_eightyOneCA_6263 : Nat.Prime 6263 := by norm_num
private theorem prime_eightyOneCA_6469 : Nat.Prime 6469 := by norm_num
private theorem prime_eightyOneCA_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_eightyOneCA_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_eightyOneCA_6791 : Nat.Prime 6791 := by norm_num
private theorem prime_eightyOneCA_6991 : Nat.Prime 6991 := by norm_num
private theorem prime_eightyOneCA_7069 : Nat.Prime 7069 := by norm_num
private theorem prime_eightyOneCA_7753 : Nat.Prime 7753 := by norm_num
private theorem prime_eightyOneCA_7841 : Nat.Prime 7841 := by norm_num
private theorem prime_eightyOneCA_8069 : Nat.Prime 8069 := by norm_num
private theorem prime_eightyOneCA_8521 : Nat.Prime 8521 := by norm_num
private theorem prime_eightyOneCA_8641 : Nat.Prime 8641 := by norm_num
private theorem prime_eightyOneCA_8677 : Nat.Prime 8677 := by norm_num
private theorem prime_eightyOneCA_9109 : Nat.Prime 9109 := by norm_num
private theorem prime_eightyOneCA_9181 : Nat.Prime 9181 := by norm_num
private theorem prime_eightyOneCA_9403 : Nat.Prime 9403 := by norm_num
private theorem prime_eightyOneCA_9749 : Nat.Prime 9749 := by norm_num
private theorem prime_eightyOneCA_10331 : Nat.Prime 10331 := by norm_num
private theorem prime_eightyOneCA_10399 : Nat.Prime 10399 := by norm_num
private theorem prime_eightyOneCA_10453 : Nat.Prime 10453 := by norm_num
private theorem prime_eightyOneCA_10463 : Nat.Prime 10463 := by norm_num
private theorem prime_eightyOneCA_10501 : Nat.Prime 10501 := by norm_num
private theorem prime_eightyOneCA_10651 : Nat.Prime 10651 := by norm_num
private theorem prime_eightyOneCA_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_eightyOneCA_10723 : Nat.Prime 10723 := by norm_num
private theorem prime_eightyOneCA_11171 : Nat.Prime 11171 := by norm_num
private theorem prime_eightyOneCA_11447 : Nat.Prime 11447 := by norm_num
private theorem prime_eightyOneCA_12899 : Nat.Prime 12899 := by norm_num
private theorem prime_eightyOneCA_13877 : Nat.Prime 13877 := by norm_num
private theorem prime_eightyOneCA_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_eightyOneCA_13913 : Nat.Prime 13913 := by norm_num
private theorem prime_eightyOneCA_14243 : Nat.Prime 14243 := by norm_num
private theorem prime_eightyOneCA_14447 : Nat.Prime 14447 := by norm_num
private theorem prime_eightyOneCA_14699 : Nat.Prime 14699 := by norm_num
private theorem prime_eightyOneCA_14897 : Nat.Prime 14897 := by norm_num
private theorem prime_eightyOneCA_15737 : Nat.Prime 15737 := by norm_num
private theorem prime_eightyOneCA_16217 : Nat.Prime 16217 := by norm_num
private theorem prime_eightyOneCA_16993 : Nat.Prime 16993 := by norm_num
private theorem prime_eightyOneCA_17569 : Nat.Prime 17569 := by norm_num
private theorem prime_eightyOneCA_17627 : Nat.Prime 17627 := by norm_num
private theorem prime_eightyOneCA_18191 : Nat.Prime 18191 := by norm_num
private theorem prime_eightyOneCA_18427 : Nat.Prime 18427 := by norm_num
private theorem prime_eightyOneCA_18731 : Nat.Prime 18731 := by norm_num
private theorem prime_eightyOneCA_18973 : Nat.Prime 18973 := by norm_num
private theorem prime_eightyOneCA_19183 : Nat.Prime 19183 := by norm_num
private theorem prime_eightyOneCA_20663 : Nat.Prime 20663 := by norm_num
private theorem prime_eightyOneCA_21059 : Nat.Prime 21059 := by norm_num
private theorem prime_eightyOneCA_22483 : Nat.Prime 22483 := by norm_num
private theorem prime_eightyOneCA_23459 : Nat.Prime 23459 := by norm_num
private theorem prime_eightyOneCA_24481 : Nat.Prime 24481 := by norm_num
private theorem prime_eightyOneCA_25969 : Nat.Prime 25969 := by norm_num
private theorem prime_eightyOneCA_26399 : Nat.Prime 26399 := by norm_num
private theorem prime_eightyOneCA_26597 : Nat.Prime 26597 := by norm_num
private theorem prime_eightyOneCA_27793 : Nat.Prime 27793 := by norm_num
private theorem prime_eightyOneCA_29201 : Nat.Prime 29201 := by norm_num
private theorem prime_eightyOneCA_29423 : Nat.Prime 29423 := by norm_num
private theorem prime_eightyOneCA_29429 : Nat.Prime 29429 := by norm_num
private theorem prime_eightyOneCA_32057 : Nat.Prime 32057 := by norm_num
private theorem prime_eightyOneCA_32069 : Nat.Prime 32069 := by norm_num
private theorem prime_eightyOneCA_32717 : Nat.Prime 32717 := by norm_num
private theorem prime_eightyOneCA_33961 : Nat.Prime 33961 := by norm_num
private theorem prime_eightyOneCA_34141 : Nat.Prime 34141 := by norm_num
private theorem prime_eightyOneCA_36037 : Nat.Prime 36037 := by norm_num
private theorem prime_eightyOneCA_37201 : Nat.Prime 37201 := by norm_num
private theorem prime_eightyOneCA_37717 : Nat.Prime 37717 := by norm_num
private theorem prime_eightyOneCA_38351 : Nat.Prime 38351 := by norm_num
private theorem prime_eightyOneCA_38669 : Nat.Prime 38669 := by norm_num
private theorem prime_eightyOneCA_43607 : Nat.Prime 43607 := by norm_num
private theorem prime_eightyOneCA_44071 : Nat.Prime 44071 := by norm_num
private theorem prime_eightyOneCA_46309 : Nat.Prime 46309 := by norm_num
private theorem prime_eightyOneCA_53611 : Nat.Prime 53611 := by norm_num
private theorem prime_eightyOneCA_56773 : Nat.Prime 56773 := by norm_num
private theorem prime_eightyOneCA_57773 : Nat.Prime 57773 := by norm_num
private theorem prime_eightyOneCA_65983 : Nat.Prime 65983 := by norm_num
private theorem prime_eightyOneCA_69191 : Nat.Prime 69191 := by norm_num
private theorem prime_eightyOneCA_73259 : Nat.Prime 73259 := by norm_num
private theorem prime_eightyOneCA_73387 : Nat.Prime 73387 := by norm_num
private theorem prime_eightyOneCA_75013 : Nat.Prime 75013 := by norm_num
private theorem prime_eightyOneCA_78203 : Nat.Prime 78203 := by norm_num
private theorem prime_eightyOneCA_79817 : Nat.Prime 79817 := by norm_num
private theorem prime_eightyOneCA_81131 : Nat.Prime 81131 := by norm_num
private theorem prime_eightyOneCA_81667 : Nat.Prime 81667 := by norm_num
private theorem prime_eightyOneCA_84319 : Nat.Prime 84319 := by norm_num
private theorem prime_eightyOneCA_87943 : Nat.Prime 87943 := by norm_num
private theorem prime_eightyOneCA_92357 : Nat.Prime 92357 := by norm_num
private theorem prime_eightyOneCA_93563 : Nat.Prime 93563 := by norm_num
private theorem prime_eightyOneCA_98327 : Nat.Prime 98327 := by norm_num
private theorem prime_eightyOneCA_98473 : Nat.Prime 98473 := by norm_num
private theorem prime_eightyOneCA_98533 : Nat.Prime 98533 := by norm_num
private theorem prime_eightyOneCA_99809 : Nat.Prime 99809 := by norm_num
private theorem prime_eightyOneCA_99971 : Nat.Prime 99971 := by norm_num
private theorem prime_eightyOneCA_109589 : Nat.Prime 109589 := by norm_num
private theorem prime_eightyOneCA_118571 : Nat.Prime 118571 := by norm_num
private theorem prime_eightyOneCA_123551 : Nat.Prime 123551 := by norm_num
private theorem prime_eightyOneCA_133403 : Nat.Prime 133403 := by norm_num
private theorem prime_eightyOneCA_134033 : Nat.Prime 134033 := by norm_num
private theorem prime_eightyOneCA_134087 : Nat.Prime 134087 := by norm_num
private theorem prime_eightyOneCA_141257 : Nat.Prime 141257 := by norm_num
private theorem prime_eightyOneCA_159199 : Nat.Prime 159199 := by norm_num
private theorem prime_eightyOneCA_162901 : Nat.Prime 162901 := by norm_num
private theorem prime_eightyOneCA_164209 : Nat.Prime 164209 := by norm_num
private theorem prime_eightyOneCA_170701 : Nat.Prime 170701 := by norm_num
private theorem prime_eightyOneCA_174569 : Nat.Prime 174569 := by norm_num
private theorem prime_eightyOneCA_184231 : Nat.Prime 184231 := by norm_num
private theorem prime_eightyOneCA_186041 : Nat.Prime 186041 := by norm_num
private theorem prime_eightyOneCA_188653 : Nat.Prime 188653 := by norm_num
private theorem prime_eightyOneCA_194687 : Nat.Prime 194687 := by norm_num
private theorem prime_eightyOneCA_194827 : Nat.Prime 194827 := by norm_num
private theorem prime_eightyOneCA_200257 : Nat.Prime 200257 := by norm_num
private theorem prime_eightyOneCA_204299 : Nat.Prime 204299 := by norm_num
private theorem prime_eightyOneCA_205607 : Nat.Prime 205607 := by norm_num
private theorem prime_eightyOneCA_213659 : Nat.Prime 213659 := by norm_num
private theorem prime_eightyOneCA_214351 : Nat.Prime 214351 := by norm_num
private theorem prime_eightyOneCA_218549 : Nat.Prime 218549 := by norm_num
private theorem prime_eightyOneCA_241393 : Nat.Prime 241393 := by norm_num
private theorem prime_eightyOneCA_250969 : Nat.Prime 250969 := by norm_num
private theorem prime_eightyOneCA_253567 : Nat.Prime 253567 := by norm_num
private theorem prime_eightyOneCA_266333 : Nat.Prime 266333 := by norm_num
private theorem prime_eightyOneCA_268789 : Nat.Prime 268789 := by norm_num
private theorem prime_eightyOneCA_282769 : Nat.Prime 282769 := by norm_num
private theorem prime_eightyOneCA_284059 : Nat.Prime 284059 := by norm_num
private theorem prime_eightyOneCA_286609 : Nat.Prime 286609 := by norm_num
private theorem prime_eightyOneCA_303539 : Nat.Prime 303539 := by norm_num
private theorem prime_eightyOneCA_305933 : Nat.Prime 305933 := by norm_num
private theorem prime_eightyOneCA_311533 : Nat.Prime 311533 := by norm_num
private theorem prime_eightyOneCA_311551 : Nat.Prime 311551 := by norm_num
private theorem prime_eightyOneCA_316759 : Nat.Prime 316759 := by norm_num
private theorem prime_eightyOneCA_356219 : Nat.Prime 356219 := by norm_num
private theorem prime_eightyOneCA_375341 : Nat.Prime 375341 := by norm_num
private theorem prime_eightyOneCA_384487 : Nat.Prime 384487 := by norm_num
private theorem prime_eightyOneCA_389579 : Nat.Prime 389579 := by norm_num
private theorem prime_eightyOneCA_399871 : Nat.Prime 399871 := by norm_num
private theorem prime_eightyOneCA_402739 : Nat.Prime 402739 := by norm_num
private theorem prime_eightyOneCA_414643 : Nat.Prime 414643 := by norm_num
private theorem prime_eightyOneCA_418079 : Nat.Prime 418079 := by norm_num
private theorem prime_eightyOneCA_434963 : Nat.Prime 434963 := by norm_num
private theorem prime_eightyOneCA_468049 : Nat.Prime 468049 := by norm_num
private theorem prime_eightyOneCA_484829 : Nat.Prime 484829 := by norm_num
private theorem prime_eightyOneCA_508349 : Nat.Prime 508349 := by norm_num
private theorem prime_eightyOneCA_518759 : Nat.Prime 518759 := by norm_num
private theorem prime_eightyOneCA_523997 : Nat.Prime 523997 := by norm_num
private theorem prime_eightyOneCA_540713 : Nat.Prime 540713 := by norm_num
private theorem prime_eightyOneCA_545449 : Nat.Prime 545449 := by norm_num
private theorem prime_eightyOneCA_546583 : Nat.Prime 546583 := by norm_num
private theorem prime_eightyOneCA_554011 : Nat.Prime 554011 := by norm_num
private theorem prime_eightyOneCA_562193 : Nat.Prime 562193 := by norm_num
private theorem prime_eightyOneCA_571877 : Nat.Prime 571877 := by norm_num
private theorem prime_eightyOneCA_610843 : Nat.Prime 610843 := by norm_num
private theorem prime_eightyOneCA_627611 : Nat.Prime 627611 := by norm_num
private theorem prime_eightyOneCA_634597 : Nat.Prime 634597 := by norm_num
private theorem prime_eightyOneCA_650081 : Nat.Prime 650081 := by norm_num
private theorem prime_eightyOneCA_657439 : Nat.Prime 657439 := by norm_num
private theorem prime_eightyOneCA_659713 : Nat.Prime 659713 := by norm_num
private theorem prime_eightyOneCA_664669 : Nat.Prime 664669 := by norm_num
private theorem prime_eightyOneCA_687359 : Nat.Prime 687359 := by norm_num
private theorem prime_eightyOneCA_739031 : Nat.Prime 739031 := by norm_num
private theorem prime_eightyOneCA_757997 : Nat.Prime 757997 := by norm_num
private theorem prime_eightyOneCA_763027 : Nat.Prime 763027 := by norm_num
private theorem prime_eightyOneCA_783533 : Nat.Prime 783533 := by norm_num
private theorem prime_eightyOneCA_816329 : Nat.Prime 816329 := by norm_num
private theorem prime_eightyOneCA_919313 : Nat.Prime 919313 := by norm_num
private theorem prime_eightyOneCA_994699 : Nat.Prime 994699 := by norm_num
private theorem prime_eightyOneCA_1000541 : Nat.Prime 1000541 := by norm_num
private theorem prime_eightyOneCA_1010983 : Nat.Prime 1010983 := by norm_num
private theorem prime_eightyOneCA_1022773 : Nat.Prime 1022773 := by norm_num
private theorem prime_eightyOneCA_1030793 : Nat.Prime 1030793 := by norm_num
private theorem prime_eightyOneCA_1040227 : Nat.Prime 1040227 := by norm_num
private theorem prime_eightyOneCA_1049677 : Nat.Prime 1049677 := by norm_num
private theorem prime_eightyOneCA_1083749 : Nat.Prime 1083749 := by norm_num
private theorem prime_eightyOneCA_1161647 : Nat.Prime 1161647 := by norm_num
private theorem prime_eightyOneCA_1169767 : Nat.Prime 1169767 := by norm_num
private theorem prime_eightyOneCA_1259051 : Nat.Prime 1259051 := by norm_num
private theorem prime_eightyOneCA_1288543 : Nat.Prime 1288543 := by norm_num
private theorem prime_eightyOneCA_1394489 : Nat.Prime 1394489 := by norm_num
private theorem prime_eightyOneCA_1396607 : Nat.Prime 1396607 := by norm_num
private theorem prime_eightyOneCA_1456099 : Nat.Prime 1456099 := by norm_num
private theorem prime_eightyOneCA_1487539 : Nat.Prime 1487539 := by norm_num
private theorem prime_eightyOneCA_1523491 : Nat.Prime 1523491 := by norm_num
private theorem prime_eightyOneCA_1526387 : Nat.Prime 1526387 := by norm_num
private theorem prime_eightyOneCA_1538909 : Nat.Prime 1538909 := by norm_num
private theorem prime_eightyOneCA_1614619 : Nat.Prime 1614619 := by norm_num
private theorem prime_eightyOneCA_1686389 : Nat.Prime 1686389 := by norm_num
private theorem prime_eightyOneCA_1689847 : Nat.Prime 1689847 := by norm_num
private theorem prime_eightyOneCA_1691219 : Nat.Prime 1691219 := by norm_num
private theorem prime_eightyOneCA_1754849 : Nat.Prime 1754849 := by norm_num
private theorem prime_eightyOneCA_1776757 : Nat.Prime 1776757 := by norm_num
private theorem prime_eightyOneCA_1875893 : Nat.Prime 1875893 := by norm_num
private theorem prime_eightyOneCA_1946059 : Nat.Prime 1946059 := by norm_num
private theorem prime_eightyOneCA_2177599 : Nat.Prime 2177599 := by norm_num
private theorem prime_eightyOneCA_2199209 : Nat.Prime 2199209 := by norm_num
private theorem prime_eightyOneCA_2238487 : Nat.Prime 2238487 := by norm_num
private theorem prime_eightyOneCA_2361269 : Nat.Prime 2361269 := by norm_num
private theorem prime_eightyOneCA_2405621 : Nat.Prime 2405621 := by norm_num
private theorem prime_eightyOneCA_2566787 : Nat.Prime 2566787 := by norm_num
private theorem prime_eightyOneCA_2643757 : Nat.Prime 2643757 := by norm_num
private theorem prime_eightyOneCA_2717107 : Nat.Prime 2717107 := by norm_num
private theorem prime_eightyOneCA_2738719 : Nat.Prime 2738719 := by norm_num
private theorem prime_eightyOneCA_2951777 : Nat.Prime 2951777 := by norm_num
private theorem prime_eightyOneCA_3182033 : Nat.Prime 3182033 := by norm_num
private theorem prime_eightyOneCA_3228109 : Nat.Prime 3228109 := by norm_num
private theorem prime_eightyOneCA_3680657 : Nat.Prime 3680657 := by norm_num
private theorem prime_eightyOneCA_3698203 : Nat.Prime 3698203 := by norm_num
private theorem prime_eightyOneCA_3897331 : Nat.Prime 3897331 := by norm_num
private theorem prime_eightyOneCA_3964381 : Nat.Prime 3964381 := by norm_num
private theorem prime_eightyOneCA_4087333 : Nat.Prime 4087333 := by norm_num
private theorem prime_eightyOneCA_4686571 : Nat.Prime 4686571 := by norm_num
private theorem prime_eightyOneCA_4710053 : Nat.Prime 4710053 := by norm_num
private theorem prime_eightyOneCA_4842653 : Nat.Prime 4842653 := by norm_num
private theorem prime_eightyOneCA_5014379 : Nat.Prime 5014379 := by norm_num
private theorem prime_eightyOneCA_5171029 : Nat.Prime 5171029 := by norm_num
private theorem prime_eightyOneCA_5612441 : Nat.Prime 5612441 := by norm_num
private theorem prime_eightyOneCA_6064771 : Nat.Prime 6064771 := by norm_num
private theorem prime_eightyOneCA_6073211 : Nat.Prime 6073211 := by norm_num
private theorem prime_eightyOneCA_6427507 : Nat.Prime 6427507 := by norm_num
private theorem prime_eightyOneCA_6772081 : Nat.Prime 6772081 := by norm_num
private theorem prime_eightyOneCA_6823891 : Nat.Prime 6823891 := by norm_num
private theorem prime_eightyOneCA_6903067 : Nat.Prime 6903067 := by norm_num
private theorem prime_eightyOneCA_7093561 : Nat.Prime 7093561 := by norm_num
private theorem prime_eightyOneCA_7492747 : Nat.Prime 7492747 := by norm_num
private theorem prime_eightyOneCA_7773481 : Nat.Prime 7773481 := by norm_num
private theorem prime_eightyOneCA_8170447 : Nat.Prime 8170447 := by norm_num
private theorem prime_eightyOneCA_8469283 : Nat.Prime 8469283 := by norm_num
private theorem prime_eightyOneCA_9079517 : Nat.Prime 9079517 := by norm_num
private theorem prime_eightyOneCA_9177547 : Nat.Prime 9177547 := by norm_num
private theorem prime_eightyOneCA_9302399 : Nat.Prime 9302399 := by norm_num
private theorem prime_eightyOneCA_9747917 : Nat.Prime 9747917 := by norm_num
private theorem prime_eightyOneCA_10198049 : Nat.Prime 10198049 := by norm_num
private theorem prime_eightyOneCA_10578571 : Nat.Prime 10578571 := by norm_num
private theorem prime_eightyOneCA_10957117 : Nat.Prime 10957117 := by norm_num
private theorem prime_eightyOneCA_11039167 : Nat.Prime 11039167 := by norm_num
private theorem prime_eightyOneCA_11770697 : Nat.Prime 11770697 := by norm_num
private theorem prime_eightyOneCA_12713749 : Nat.Prime 12713749 := by norm_num
private theorem prime_eightyOneCA_13211083 : Nat.Prime 13211083 := by norm_num
private theorem prime_eightyOneCA_14039057 : Nat.Prime 14039057 := by norm_num
private theorem prime_eightyOneCA_14168489 : Nat.Prime 14168489 := by norm_num
private theorem prime_eightyOneCA_15155747 : Nat.Prime 15155747 := by norm_num
private theorem prime_eightyOneCA_15201883 : Nat.Prime 15201883 := by norm_num
private theorem prime_eightyOneCA_16670851 : Nat.Prime 16670851 := by norm_num
private theorem prime_eightyOneCA_17750767 : Nat.Prime 17750767 := by norm_num
private theorem prime_eightyOneCA_19050091 : Nat.Prime 19050091 := by norm_num
private theorem prime_eightyOneCA_19422497 : Nat.Prime 19422497 := by norm_num
private theorem prime_eightyOneCA_19843321 : Nat.Prime 19843321 := by norm_num
private theorem prime_eightyOneCA_21654383 : Nat.Prime 21654383 := by norm_num
private theorem prime_eightyOneCA_24060173 : Nat.Prime 24060173 := by norm_num
private theorem prime_eightyOneCA_24120007 : Nat.Prime 24120007 := by norm_num
private theorem prime_eightyOneCA_25400269 : Nat.Prime 25400269 := by norm_num
private theorem prime_eightyOneCA_27474289 : Nat.Prime 27474289 := by norm_num
private theorem prime_eightyOneCA_30820241 : Nat.Prime 30820241 := by norm_num
private theorem prime_eightyOneCA_31067189 : Nat.Prime 31067189 := by norm_num
private theorem prime_eightyOneCA_31121527 : Nat.Prime 31121527 := by norm_num
private theorem prime_eightyOneCA_35647831 : Nat.Prime 35647831 := by
  apply lucas_primality 35647831 (7 : ZMod 35647831)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (31, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (31, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod = 35647831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_4259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35647831) ^ 17823915 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 35647831) ^ 11882610 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 35647831) ^ 7129566 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 35647831) ^ 1149930 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 35647831) ^ 8370 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_36530171 : Nat.Prime 36530171 := by
  apply lucas_primality 36530171 (2 : ZMod 36530171)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (421, 1), (8677, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (421, 1), (8677, 1)] : List FactorBlock).map factorBlockValue).prod = 36530171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_421
      · exact prime_eightyOneCA_8677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36530171) ^ 18265085 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36530171) ^ 7306034 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36530171) ^ 86770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36530171) ^ 4210 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_36754589 : Nat.Prime 36754589 := by
  apply lucas_primality 36754589 (2 : ZMod 36754589)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (19, 1), (37201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (19, 1), (37201, 1)] : List FactorBlock).map factorBlockValue).prod = 36754589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_37201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36754589) ^ 18377294 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36754589) ^ 2827276 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36754589) ^ 1934452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36754589) ^ 988 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_38316121 : Nat.Prime 38316121 := by
  apply lucas_primality 38316121 (11 : ZMod 38316121)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (83, 1), (3847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (83, 1), (3847, 1)] : List FactorBlock).map factorBlockValue).prod = 38316121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_3847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 38316121) ^ 19158060 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 38316121) ^ 12772040 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 38316121) ^ 7663224 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 38316121) ^ 461640 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 38316121) ^ 9960 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_44156669 : Nat.Prime 44156669 := by
  apply lucas_primality 44156669 (2 : ZMod 44156669)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11039167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11039167, 1)] : List FactorBlock).map factorBlockValue).prod = 44156669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11039167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44156669) ^ 22078334 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 44156669) ^ 4 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_44726819 : Nat.Prime 44726819 := by
  apply lucas_primality 44726819 (2 : ZMod 44726819)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (545449, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (545449, 1)] : List FactorBlock).map factorBlockValue).prod = 44726819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_545449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44726819) ^ 22363409 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 44726819) ^ 1090898 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 44726819) ^ 82 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_45728437 : Nat.Prime 45728437 := by
  apply lucas_primality 45728437 (2 : ZMod 45728437)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (17, 1), (43, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (17, 1), (43, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod = 45728437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45728437) ^ 22864218 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45728437) ^ 15242812 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45728437) ^ 3517572 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45728437) ^ 2689908 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45728437) ^ 1063452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45728437) ^ 114036 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_47522929 : Nat.Prime 47522929 := by
  apply lucas_primality 47522929 (7 : ZMod 47522929)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (761, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (761, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod = 47522929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_761
      · exact prime_eightyOneCA_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47522929) ^ 23761464 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 47522929) ^ 15840976 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 47522929) ^ 62448 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 47522929) ^ 36528 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_50471263 : Nat.Prime 50471263 := by
  apply lucas_primality 50471263 (3 : ZMod 50471263)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (311551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (311551, 1)] : List FactorBlock).map factorBlockValue).prod = 50471263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_311551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50471263) ^ 25235631 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 50471263) ^ 16823754 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 50471263) ^ 162 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_58275281 : Nat.Prime 58275281 := by
  apply lucas_primality 58275281 (6 : ZMod 58275281)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (19, 1), (5477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (19, 1), (5477, 1)] : List FactorBlock).map factorBlockValue).prod = 58275281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_5477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 58275281) ^ 29137640 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 58275281) ^ 11655056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 58275281) ^ 8325040 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 58275281) ^ 3067120 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 58275281) ^ 10640 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_59272979 : Nat.Prime 59272979 := by
  apply lucas_primality 59272979 (2 : ZMod 59272979)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (1288543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (1288543, 1)] : List FactorBlock).map factorBlockValue).prod = 59272979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_1288543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59272979) ^ 29636489 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59272979) ^ 2577086 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59272979) ^ 46 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_62227423 : Nat.Prime 62227423 := by
  apply lucas_primality 62227423 (3 : ZMod 62227423)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (41, 1), (84319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (41, 1), (84319, 1)] : List FactorBlock).map factorBlockValue).prod = 62227423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_84319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62227423) ^ 31113711 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227423) ^ 20742474 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227423) ^ 1517742 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62227423) ^ 738 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_64471003 : Nat.Prime 64471003 := by
  apply lucas_primality 64471003 (3 : ZMod 64471003)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29, 1), (53, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29, 1), (53, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod = 64471003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_53
      · exact prime_eightyOneCA_6991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64471003) ^ 32235501 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 64471003) ^ 21490334 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 64471003) ^ 2223138 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 64471003) ^ 1216434 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 64471003) ^ 9222 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_67184023 : Nat.Prime 67184023 := by
  apply lucas_primality 67184023 (5 : ZMod 67184023)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (421, 1), (26597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (421, 1), (26597, 1)] : List FactorBlock).map factorBlockValue).prod = 67184023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_421
      · exact prime_eightyOneCA_26597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67184023) ^ 33592011 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 67184023) ^ 22394674 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 67184023) ^ 159582 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 67184023) ^ 2526 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_73176119 : Nat.Prime 73176119 := by
  apply lucas_primality 73176119 (7 : ZMod 73176119)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5483, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5483, 1), (6673, 1)] : List FactorBlock).map factorBlockValue).prod = 73176119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5483
      · exact prime_eightyOneCA_6673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 73176119) ^ 36588059 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 73176119) ^ 13346 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 73176119) ^ 10966 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_77352029 : Nat.Prime 77352029 := by
  apply lucas_primality 77352029 (2 : ZMod 77352029)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (1487539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (1487539, 1)] : List FactorBlock).map factorBlockValue).prod = 77352029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_1487539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77352029) ^ 38676014 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 77352029) ^ 5950156 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 77352029) ^ 52 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_87574387 : Nat.Prime 87574387 := by
  apply lucas_primality 87574387 (3 : ZMod 87574387)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (634597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (634597, 1)] : List FactorBlock).map factorBlockValue).prod = 87574387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_634597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87574387) ^ 43787193 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 87574387) ^ 29191462 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 87574387) ^ 3807582 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 87574387) ^ 138 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_90934483 : Nat.Prime 90934483 := by
  apply lucas_primality 90934483 (2 : ZMod 90934483)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (15155747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (15155747, 1)] : List FactorBlock).map factorBlockValue).prod = 90934483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_15155747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90934483) ^ 45467241 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 90934483) ^ 30311494 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 90934483) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_91823437 : Nat.Prime 91823437 := by
  apply lucas_primality 91823437 (7 : ZMod 91823437)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (41, 1), (89, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (41, 1), (89, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod = 91823437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_89
      · exact prime_eightyOneCA_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 91823437) ^ 45911718 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 91823437) ^ 30607812 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 91823437) ^ 2239596 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 91823437) ^ 1031724 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 91823437) ^ 394092 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_94201061 : Nat.Prime 94201061 := by
  apply lucas_primality 94201061 (2 : ZMod 94201061)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4710053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4710053, 1)] : List FactorBlock).map factorBlockValue).prod = 94201061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_4710053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94201061) ^ 47100530 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 94201061) ^ 18840212 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 94201061) ^ 20 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_94520999 : Nat.Prime 94520999 := by
  apply lucas_primality 94520999 (11 : ZMod 94520999)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (13, 1), (167, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (13, 1), (167, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod = 94520999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_167
      · exact prime_eightyOneCA_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 94520999) ^ 47260499 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 94520999) ^ 8592818 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 94520999) ^ 7270846 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 94520999) ^ 565994 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 94520999) ^ 47762 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_94825253 : Nat.Prime 94825253 := by
  apply lucas_primality 94825253 (2 : ZMod 94825253)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (1394489, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (1394489, 1)] : List FactorBlock).map factorBlockValue).prod = 94825253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_1394489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94825253) ^ 47412626 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 94825253) ^ 5577956 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 94825253) ^ 68 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_99618733 : Nat.Prime 99618733 := by
  apply lucas_primality 99618733 (2 : ZMod 99618733)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (449, 1), (6163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (449, 1), (6163, 1)] : List FactorBlock).map factorBlockValue).prod = 99618733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_449
      · exact prime_eightyOneCA_6163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 99618733) ^ 49809366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99618733) ^ 33206244 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99618733) ^ 221868 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99618733) ^ 16164 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_101842523 : Nat.Prime 101842523 := by
  apply lucas_primality 101842523 (2 : ZMod 101842523)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (727, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (727, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod = 101842523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_89
      · exact prime_eightyOneCA_727
      · exact prime_eightyOneCA_787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101842523) ^ 50921261 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101842523) ^ 1144298 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101842523) ^ 140086 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 101842523) ^ 129406 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_107913653 : Nat.Prime 107913653 := by
  apply lucas_primality 107913653 (3 : ZMod 107913653)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (101, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (101, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod = 107913653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107913653) ^ 53956826 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 107913653) ^ 15416236 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 107913653) ^ 9810332 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 107913653) ^ 1068452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 107913653) ^ 31108 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_109715213 : Nat.Prime 109715213 := by
  apply lucas_primality 109715213 (2 : ZMod 109715213)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (37, 1), (43607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (37, 1), (43607, 1)] : List FactorBlock).map factorBlockValue).prod = 109715213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_43607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 109715213) ^ 54857606 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 109715213) ^ 6453836 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 109715213) ^ 2965276 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 109715213) ^ 2516 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_113231647 : Nat.Prime 113231647 := by
  apply lucas_primality 113231647 (3 : ZMod 113231647)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (571877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (571877, 1)] : List FactorBlock).map factorBlockValue).prod = 113231647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_571877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 113231647) ^ 56615823 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 113231647) ^ 37743882 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 113231647) ^ 10293786 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 113231647) ^ 198 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_140818963 : Nat.Prime 140818963 := by
  apply lucas_primality 140818963 (2 : ZMod 140818963)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (83, 1), (282769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (83, 1), (282769, 1)] : List FactorBlock).map factorBlockValue).prod = 140818963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_282769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 140818963) ^ 70409481 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 140818963) ^ 46939654 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 140818963) ^ 1696614 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 140818963) ^ 498 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_149268881 : Nat.Prime 149268881 := by
  apply lucas_primality 149268881 (3 : ZMod 149268881)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (163, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (163, 1), (11447, 1)] : List FactorBlock).map factorBlockValue).prod = 149268881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_163
      · exact prime_eightyOneCA_11447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 149268881) ^ 74634440 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149268881) ^ 29853776 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149268881) ^ 915760 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 149268881) ^ 13040 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_154704059 : Nat.Prime 154704059 := by
  apply lucas_primality 154704059 (2 : ZMod 154704059)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (77352029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (77352029, 1)] : List FactorBlock).map factorBlockValue).prod = 154704059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_77352029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 154704059) ^ 77352029 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 154704059) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_162866981 : Nat.Prime 162866981 := by
  apply lucas_primality 162866981 (2 : ZMod 162866981)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (293, 1), (27793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (293, 1), (27793, 1)] : List FactorBlock).map factorBlockValue).prod = 162866981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_293
      · exact prime_eightyOneCA_27793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 162866981) ^ 81433490 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 162866981) ^ 32573396 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 162866981) ^ 555860 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 162866981) ^ 5860 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_174189877 : Nat.Prime 174189877 := by
  apply lucas_primality 174189877 (2 : ZMod 174189877)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (1187, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (1187, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod = 174189877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_1187
      · exact prime_eightyOneCA_1747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174189877) ^ 87094938 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 174189877) ^ 58063292 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 174189877) ^ 24884268 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 174189877) ^ 146748 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 174189877) ^ 99708 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_179089549 : Nat.Prime 179089549 := by
  apply lucas_primality 179089549 (2 : ZMod 179089549)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (71, 1), (97, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (71, 1), (97, 1), (197, 1)] : List FactorBlock).map factorBlockValue).prod = 179089549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_71
      · exact prime_eightyOneCA_97
      · exact prime_eightyOneCA_197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 179089549) ^ 89544774 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 179089549) ^ 59696516 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 179089549) ^ 16280868 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 179089549) ^ 2522388 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 179089549) ^ 1846284 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 179089549) ^ 909084 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_184469633 : Nat.Prime 184469633 := by
  apply lucas_primality 184469633 (3 : ZMod 184469633)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (19, 1), (101, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (19, 1), (101, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod = 184469633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 184469633) ^ 92234816 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 184469633) ^ 9708928 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 184469633) ^ 1826432 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 184469633) ^ 245632 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_185307637 : Nat.Prime 185307637 := by
  apply lucas_primality 185307637 (2 : ZMod 185307637)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (97, 1), (159199, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (97, 1), (159199, 1)] : List FactorBlock).map factorBlockValue).prod = 185307637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_97
      · exact prime_eightyOneCA_159199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 185307637) ^ 92653818 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 185307637) ^ 61769212 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 185307637) ^ 1910388 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 185307637) ^ 1164 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_194504143 : Nat.Prime 194504143 := by
  apply lucas_primality 194504143 (6 : ZMod 194504143)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (47, 1), (98533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (47, 1), (98533, 1)] : List FactorBlock).map factorBlockValue).prod = 194504143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_47
      · exact prime_eightyOneCA_98533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 194504143) ^ 97252071 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 194504143) ^ 64834714 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 194504143) ^ 27786306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 194504143) ^ 4138386 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 194504143) ^ 1974 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_201141029 : Nat.Prime 201141029 := by
  apply lucas_primality 201141029 (2 : ZMod 201141029)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (37, 1), (123551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (37, 1), (123551, 1)] : List FactorBlock).map factorBlockValue).prod = 201141029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_123551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201141029) ^ 100570514 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 201141029) ^ 18285548 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 201141029) ^ 5436244 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 201141029) ^ 1628 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_203685047 : Nat.Prime 203685047 := by
  apply lucas_primality 203685047 (5 : ZMod 203685047)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101842523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101842523, 1)] : List FactorBlock).map factorBlockValue).prod = 203685047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_101842523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 203685047) ^ 101842523 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 203685047) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_210603919 : Nat.Prime 210603919 := by
  apply lucas_primality 210603919 (7 : ZMod 210603919)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (5014379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (5014379, 1)] : List FactorBlock).map factorBlockValue).prod = 210603919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_5014379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 210603919) ^ 105301959 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 210603919) ^ 70201306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 210603919) ^ 30086274 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 210603919) ^ 42 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_216019099 : Nat.Prime 216019099 := by
  apply lucas_primality 216019099 (2 : ZMod 216019099)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (31, 1), (37, 1), (10463, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (31, 1), (37, 1), (10463, 1)] : List FactorBlock).map factorBlockValue).prod = 216019099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_10463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 216019099) ^ 108009549 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 216019099) ^ 72006366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 216019099) ^ 6968358 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 216019099) ^ 5838354 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 216019099) ^ 20646 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_230861353 : Nat.Prime 230861353 := by
  apply lucas_primality 230861353 (10 : ZMod 230861353)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (37, 1), (499, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (37, 1), (499, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod = 230861353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_499
      · exact prime_eightyOneCA_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 230861353) ^ 115430676 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 230861353) ^ 76953784 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 230861353) ^ 6239496 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 230861353) ^ 462648 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 230861353) ^ 443112 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_232759567 : Nat.Prime 232759567 := by
  apply lucas_primality 232759567 (3 : ZMod 232759567)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (994699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (994699, 1)] : List FactorBlock).map factorBlockValue).prod = 232759567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_994699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 232759567) ^ 116379783 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 232759567) ^ 77586522 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 232759567) ^ 17904582 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 232759567) ^ 234 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_237102641 : Nat.Prime 237102641 := by
  apply lucas_primality 237102641 (3 : ZMod 237102641)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (1579, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (1579, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod = 237102641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1579
      · exact prime_eightyOneCA_1877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 237102641) ^ 118551320 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 237102641) ^ 47420528 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 237102641) ^ 150160 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 237102641) ^ 126320 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_243758561 : Nat.Prime 243758561 := by
  apply lucas_primality 243758561 (3 : ZMod 243758561)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (1523491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (1523491, 1)] : List FactorBlock).map factorBlockValue).prod = 243758561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1523491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 243758561) ^ 121879280 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 243758561) ^ 48751712 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 243758561) ^ 160 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_245113411 : Nat.Prime 245113411 := by
  apply lucas_primality 245113411 (2 : ZMod 245113411)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (8170447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (8170447, 1)] : List FactorBlock).map factorBlockValue).prod = 245113411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_8170447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 245113411) ^ 122556705 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 245113411) ^ 81704470 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 245113411) ^ 49022682 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 245113411) ^ 30 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_248510413 : Nat.Prime 248510413 := by
  apply lucas_primality 248510413 (2 : ZMod 248510413)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (6903067, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (6903067, 1)] : List FactorBlock).map factorBlockValue).prod = 248510413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_6903067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 248510413) ^ 124255206 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 248510413) ^ 82836804 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 248510413) ^ 36 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_262625021 : Nat.Prime 262625021 := by
  apply lucas_primality 262625021 (3 : ZMod 262625021)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (1875893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (1875893, 1)] : List FactorBlock).map factorBlockValue).prod = 262625021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_1875893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 262625021) ^ 131312510 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 262625021) ^ 52525004 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 262625021) ^ 37517860 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 262625021) ^ 140 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_289233419 : Nat.Prime 289233419 := by
  apply lucas_primality 289233419 (2 : ZMod 289233419)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (811, 1), (7753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (811, 1), (7753, 1)] : List FactorBlock).map factorBlockValue).prod = 289233419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_811
      · exact prime_eightyOneCA_7753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 289233419) ^ 144616709 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 289233419) ^ 12575366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 289233419) ^ 356638 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 289233419) ^ 37306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_411223039 : Nat.Prime 411223039 := by
  apply lucas_primality 411223039 (3 : ZMod 411223039)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (59, 1), (1161647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (59, 1), (1161647, 1)] : List FactorBlock).map factorBlockValue).prod = 411223039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_59
      · exact prime_eightyOneCA_1161647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 411223039) ^ 205611519 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 411223039) ^ 137074346 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 411223039) ^ 6969882 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 411223039) ^ 354 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_458530799 : Nat.Prime 458530799 := by
  apply lucas_primality 458530799 (11 : ZMod 458530799)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (41, 1), (508349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (41, 1), (508349, 1)] : List FactorBlock).map factorBlockValue).prod = 458530799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_508349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 458530799) ^ 229265399 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 458530799) ^ 41684618 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 458530799) ^ 11183678 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 458530799) ^ 902 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_470819567 : Nat.Prime 470819567 := by
  apply lucas_primality 470819567 (5 : ZMod 470819567)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (2137, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (2137, 1), (15737, 1)] : List FactorBlock).map factorBlockValue).prod = 470819567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_2137
      · exact prime_eightyOneCA_15737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 470819567) ^ 235409783 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 470819567) ^ 67259938 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 470819567) ^ 220318 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 470819567) ^ 29918 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_481203461 : Nat.Prime 481203461 := by
  apply lucas_primality 481203461 (2 : ZMod 481203461)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (24060173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (24060173, 1)] : List FactorBlock).map factorBlockValue).prod = 481203461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_24060173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 481203461) ^ 240601730 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 481203461) ^ 96240692 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 481203461) ^ 20 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_514564247 : Nat.Prime 514564247 := by
  apply lucas_primality 514564247 (5 : ZMod 514564247)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (36754589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (36754589, 1)] : List FactorBlock).map factorBlockValue).prod = 514564247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_36754589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 514564247) ^ 257282123 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 514564247) ^ 73509178 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 514564247) ^ 14 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_524492291 : Nat.Prime 524492291 := by
  apply lucas_primality 524492291 (2 : ZMod 524492291)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (7492747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (7492747, 1)] : List FactorBlock).map factorBlockValue).prod = 524492291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_7492747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 524492291) ^ 262246145 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 524492291) ^ 104898458 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 524492291) ^ 74927470 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 524492291) ^ 70 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_593486083 : Nat.Prime 593486083 := by
  apply lucas_primality 593486083 (3 : ZMod 593486083)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (17, 1), (92357, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (17, 1), (92357, 1)] : List FactorBlock).map factorBlockValue).prod = 593486083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_92357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 593486083) ^ 296743041 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 593486083) ^ 197828694 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 593486083) ^ 84783726 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 593486083) ^ 34910946 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 593486083) ^ 6426 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_603311179 : Nat.Prime 603311179 := by
  apply lucas_primality 603311179 (2 : ZMod 603311179)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (101, 1), (977, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (101, 1), (977, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod = 603311179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_977
      · exact prime_eightyOneCA_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 603311179) ^ 301655589 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 603311179) ^ 201103726 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 603311179) ^ 5973378 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 603311179) ^ 617514 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 603311179) ^ 592062 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_649382501 : Nat.Prime 649382501 := by
  apply lucas_primality 649382501 (2 : ZMod 649382501)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 4), (13, 2), (29, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 4), (13, 2), (29, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod = 649382501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_53
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 649382501) ^ 324691250 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 649382501) ^ 129876500 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 649382501) ^ 49952500 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 649382501) ^ 22392500 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 649382501) ^ 12252500 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_652078019 : Nat.Prime 652078019 := by
  apply lucas_primality 652078019 (2 : ZMod 652078019)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101, 1), (3228109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101, 1), (3228109, 1)] : List FactorBlock).map factorBlockValue).prod = 652078019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_3228109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 652078019) ^ 326039009 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 652078019) ^ 6456218 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 652078019) ^ 202 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_738209083 : Nat.Prime 738209083 := by
  apply lucas_primality 738209083 (2 : ZMod 738209083)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (67, 1), (141257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (67, 1), (141257, 1)] : List FactorBlock).map factorBlockValue).prod = 738209083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_67
      · exact prime_eightyOneCA_141257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 738209083) ^ 369104541 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 738209083) ^ 246069694 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 738209083) ^ 56785314 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 738209083) ^ 11018046 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 738209083) ^ 5226 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_744628177 : Nat.Prime 744628177 := by
  apply lucas_primality 744628177 (5 : ZMod 744628177)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5171029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5171029, 1)] : List FactorBlock).map factorBlockValue).prod = 744628177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5171029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 744628177) ^ 372314088 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 744628177) ^ 248209392 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 744628177) ^ 144 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_871851583 : Nat.Prime 871851583 := by
  apply lucas_primality 871851583 (3 : ZMod 871851583)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (2579, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (2579, 1), (2683, 1)] : List FactorBlock).map factorBlockValue).prod = 871851583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_2579
      · exact prime_eightyOneCA_2683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 871851583) ^ 435925791 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 871851583) ^ 290617194 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 871851583) ^ 124550226 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 871851583) ^ 338058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 871851583) ^ 324954 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1048984583 : Nat.Prime 1048984583 := by
  apply lucas_primality 1048984583 (5 : ZMod 1048984583)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (524492291, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (524492291, 1)] : List FactorBlock).map factorBlockValue).prod = 1048984583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_524492291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1048984583) ^ 524492291 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1048984583) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1066811299 : Nat.Prime 1066811299 := by
  apply lucas_primality 1066811299 (2 : ZMod 1066811299)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (25400269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (25400269, 1)] : List FactorBlock).map factorBlockValue).prod = 1066811299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_25400269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1066811299) ^ 533405649 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1066811299) ^ 355603766 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1066811299) ^ 152401614 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1066811299) ^ 42 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1222110283 : Nat.Prime 1222110283 := by
  apply lucas_primality 1222110283 (5 : ZMod 1222110283)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (203685047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (203685047, 1)] : List FactorBlock).map factorBlockValue).prod = 1222110283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_203685047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1222110283) ^ 611055141 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222110283) ^ 407370094 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1222110283) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1308361627 : Nat.Prime 1308361627 := by
  apply lucas_primality 1308361627 (2 : ZMod 1308361627)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11, 2), (13, 1), (73, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11, 2), (13, 1), (73, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod = 1308361627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_73
      · exact prime_eightyOneCA_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1308361627) ^ 654180813 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308361627) ^ 436120542 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308361627) ^ 118941966 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308361627) ^ 100643202 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308361627) ^ 17922762 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1308361627) ^ 6200766 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1385168119 : Nat.Prime 1385168119 := by
  apply lucas_primality 1385168119 (3 : ZMod 1385168119)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (230861353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (230861353, 1)] : List FactorBlock).map factorBlockValue).prod = 1385168119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_230861353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1385168119) ^ 692584059 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1385168119) ^ 461722706 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1385168119) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1731643981 : Nat.Prime 1731643981 := by
  apply lucas_primality 1731643981 (6 : ZMod 1731643981)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (251, 1), (10453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (251, 1), (10453, 1)] : List FactorBlock).map factorBlockValue).prod = 1731643981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_251
      · exact prime_eightyOneCA_10453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1731643981) ^ 865821990 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1731643981) ^ 577214660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1731643981) ^ 346328796 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1731643981) ^ 157422180 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1731643981) ^ 6898980 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1731643981) ^ 165660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1790724079 : Nat.Prime 1790724079 := by
  apply lucas_primality 1790724079 (6 : ZMod 1790724079)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (11, 1), (13, 1), (43, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (11, 1), (13, 1), (43, 1), (5393, 1)] : List FactorBlock).map factorBlockValue).prod = 1790724079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_5393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1790724079) ^ 895362039 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790724079) ^ 596908026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790724079) ^ 162793098 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790724079) ^ 137748006 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790724079) ^ 41644746 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790724079) ^ 332046 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1971808589 : Nat.Prime 1971808589 := by
  apply lucas_primality 1971808589 (2 : ZMod 1971808589)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (2143, 1), (6217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (2143, 1), (6217, 1)] : List FactorBlock).map factorBlockValue).prod = 1971808589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_2143
      · exact prime_eightyOneCA_6217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1971808589) ^ 985904294 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971808589) ^ 53292124 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971808589) ^ 920116 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971808589) ^ 317164 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2000558627 : Nat.Prime 2000558627 := by
  apply lucas_primality 2000558627 (7 : ZMod 2000558627)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (90934483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (90934483, 1)] : List FactorBlock).map factorBlockValue).prod = 2000558627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_90934483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2000558627) ^ 1000279313 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2000558627) ^ 181868966 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2000558627) ^ 22 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2283483913 : Nat.Prime 2283483913 := by
  apply lucas_primality 2283483913 (10 : ZMod 2283483913)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (311, 1), (305933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (311, 1), (305933, 1)] : List FactorBlock).map factorBlockValue).prod = 2283483913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_311
      · exact prime_eightyOneCA_305933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2283483913) ^ 1141741956 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2283483913) ^ 761161304 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2283483913) ^ 7342392 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2283483913) ^ 7464 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2450614193 : Nat.Prime 2450614193 := by
  apply lucas_primality 2450614193 (3 : ZMod 2450614193)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (17, 1), (37, 1), (18731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (17, 1), (37, 1), (18731, 1)] : List FactorBlock).map factorBlockValue).prod = 2450614193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_18731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2450614193) ^ 1225307096 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2450614193) ^ 188508784 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2450614193) ^ 144153776 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2450614193) ^ 66232816 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2450614193) ^ 130832 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2535497603 : Nat.Prime 2535497603 := by
  apply lucas_primality 2535497603 (2 : ZMod 2535497603)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (3917, 1), (29423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (3917, 1), (29423, 1)] : List FactorBlock).map factorBlockValue).prod = 2535497603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_3917
      · exact prime_eightyOneCA_29423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2535497603) ^ 1267748801 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535497603) ^ 230499782 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535497603) ^ 647306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2535497603) ^ 86174 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2975216477 : Nat.Prime 2975216477 := by
  apply lucas_primality 2975216477 (2 : ZMod 2975216477)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (109, 1), (6823891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (109, 1), (6823891, 1)] : List FactorBlock).map factorBlockValue).prod = 2975216477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_109
      · exact prime_eightyOneCA_6823891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2975216477) ^ 1487608238 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975216477) ^ 27295564 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975216477) ^ 436 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2996119639 : Nat.Prime 2996119639 := by
  apply lucas_primality 2996119639 (6 : ZMod 2996119639)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3011, 1), (18427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3011, 1), (18427, 1)] : List FactorBlock).map factorBlockValue).prod = 2996119639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_3011
      · exact prime_eightyOneCA_18427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2996119639) ^ 1498059819 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2996119639) ^ 998706546 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2996119639) ^ 995058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2996119639) ^ 162594 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_3739915111 : Nat.Prime 3739915111 := by
  apply lucas_primality 3739915111 (3 : ZMod 3739915111)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29, 1), (43, 1), (99971, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29, 1), (43, 1), (99971, 1)] : List FactorBlock).map factorBlockValue).prod = 3739915111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_99971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3739915111) ^ 1869957555 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3739915111) ^ 1246638370 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3739915111) ^ 747983022 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3739915111) ^ 128962590 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3739915111) ^ 86974770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3739915111) ^ 37410 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_3908313169 : Nat.Prime 3908313169 := by
  apply lucas_primality 3908313169 (7 : ZMod 3908313169)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (2539, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (2539, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod = 3908313169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_2539
      · exact prime_eightyOneCA_32069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3908313169) ^ 1954156584 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3908313169) ^ 1302771056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3908313169) ^ 1539312 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3908313169) ^ 121872 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_3939805151 : Nat.Prime 3939805151 := by
  apply lucas_primality 3939805151 (7 : ZMod 3939805151)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (29, 1), (2717107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (29, 1), (2717107, 1)] : List FactorBlock).map factorBlockValue).prod = 3939805151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_2717107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3939805151) ^ 1969902575 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3939805151) ^ 787961030 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3939805151) ^ 135855350 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 3939805151) ^ 1450 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4429254499 : Nat.Prime 4429254499 := by
  apply lucas_primality 4429254499 (3 : ZMod 4429254499)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (738209083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (738209083, 1)] : List FactorBlock).map factorBlockValue).prod = 4429254499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_738209083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4429254499) ^ 2214627249 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4429254499) ^ 1476418166 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4429254499) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4651772179 : Nat.Prime 4651772179 := by
  apply lucas_primality 4651772179 (10 : ZMod 4651772179)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (41, 1), (71, 1), (266333, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (41, 1), (71, 1), (266333, 1)] : List FactorBlock).map factorBlockValue).prod = 4651772179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_71
      · exact prime_eightyOneCA_266333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4651772179) ^ 2325886089 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4651772179) ^ 1550590726 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4651772179) ^ 113457858 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4651772179) ^ 65517918 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4651772179) ^ 17466 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4701315503 : Nat.Prime 4701315503 := by
  apply lucas_primality 4701315503 (10 : ZMod 4701315503)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (19, 1), (2399, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (19, 1), (2399, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod = 4701315503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_2399
      · exact prime_eightyOneCA_3967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4701315503) ^ 2350657751 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4701315503) ^ 361639654 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4701315503) ^ 247437658 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4701315503) ^ 1959698 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 4701315503) ^ 1185106 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4930022711 : Nat.Prime 4930022711 := by
  apply lucas_primality 4930022711 (11 : ZMod 4930022711)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (353, 1), (1396607, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (353, 1), (1396607, 1)] : List FactorBlock).map factorBlockValue).prod = 4930022711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_353
      · exact prime_eightyOneCA_1396607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4930022711) ^ 2465011355 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 4930022711) ^ 986004542 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 4930022711) ^ 13966070 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 4930022711) ^ 3530 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_5217421921 : Nat.Prime 5217421921 := by
  apply lucas_primality 5217421921 (11 : ZMod 5217421921)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (59, 1), (184231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (59, 1), (184231, 1)] : List FactorBlock).map factorBlockValue).prod = 5217421921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_59
      · exact prime_eightyOneCA_184231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5217421921) ^ 2608710960 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 5217421921) ^ 1739140640 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 5217421921) ^ 1043484384 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 5217421921) ^ 88430880 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 5217421921) ^ 28320 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_6172814173 : Nat.Prime 6172814173 := by
  apply lucas_primality 6172814173 (2 : ZMod 6172814173)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (17, 1), (101, 1), (127, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (17, 1), (101, 1), (127, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod = 6172814173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_127
      · exact prime_eightyOneCA_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6172814173) ^ 3086407086 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 2057604724 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 881830596 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 363106716 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 61116972 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 48604836 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6172814173) ^ 18316956 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_7319778623 : Nat.Prime 7319778623 := by
  apply lucas_primality 7319778623 (5 : ZMod 7319778623)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (107, 1), (179, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (107, 1), (179, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod = 7319778623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_107
      · exact prime_eightyOneCA_179
      · exact prime_eightyOneCA_14699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7319778623) ^ 3659889311 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7319778623) ^ 563059894 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7319778623) ^ 68409146 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7319778623) ^ 40892618 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7319778623) ^ 497978 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_8205723587 : Nat.Prime 8205723587 := by
  apply lucas_primality 8205723587 (2 : ZMod 8205723587)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (21059, 1), (194827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (21059, 1), (194827, 1)] : List FactorBlock).map factorBlockValue).prod = 8205723587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_21059
      · exact prime_eightyOneCA_194827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8205723587) ^ 4102861793 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8205723587) ^ 389654 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8205723587) ^ 42118 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_9860045423 : Nat.Prime 9860045423 := by
  apply lucas_primality 9860045423 (5 : ZMod 9860045423)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4930022711, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4930022711, 1)] : List FactorBlock).map factorBlockValue).prod = 9860045423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_4930022711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 9860045423) ^ 4930022711 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9860045423) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10123407929 : Nat.Prime 10123407929 := by
  apply lucas_primality 10123407929 (6 : ZMod 10123407929)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (29, 1), (2566787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (29, 1), (2566787, 1)] : List FactorBlock).map factorBlockValue).prod = 10123407929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_2566787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10123407929) ^ 5061703964 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10123407929) ^ 595494584 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10123407929) ^ 349083032 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10123407929) ^ 3944 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10698951691 : Nat.Prime 10698951691 := by
  apply lucas_primality 10698951691 (2 : ZMod 10698951691)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (7, 1), (43, 1), (47, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (7, 1), (43, 1), (47, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod = 10698951691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_47
      · exact prime_eightyOneCA_2801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10698951691) ^ 5349475845 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 3566317230 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 2139790338 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 1528421670 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 248812830 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 227637270 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10698951691) ^ 3819690 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10749220747 : Nat.Prime 10749220747 := by
  apply lucas_primality 10749220747 (2 : ZMod 10749220747)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (162866981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (162866981, 1)] : List FactorBlock).map factorBlockValue).prod = 10749220747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_162866981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10749220747) ^ 5374610373 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10749220747) ^ 3583073582 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10749220747) ^ 977201886 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10749220747) ^ 66 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10927623977 : Nat.Prime 10927623977 := by
  apply lucas_primality 10927623977 (3 : ZMod 10927623977)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (359, 1), (200257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (359, 1), (200257, 1)] : List FactorBlock).map factorBlockValue).prod = 10927623977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_359
      · exact prime_eightyOneCA_200257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10927623977) ^ 5463811988 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10927623977) ^ 575138104 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10927623977) ^ 30439064 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10927623977) ^ 54568 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_11432725553 : Nat.Prime 11432725553 := by
  apply lucas_primality 11432725553 (3 : ZMod 11432725553)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (23, 1), (31067189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (23, 1), (31067189, 1)] : List FactorBlock).map factorBlockValue).prod = 11432725553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_31067189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11432725553) ^ 5716362776 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11432725553) ^ 497075024 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11432725553) ^ 368 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_15478312159 : Nat.Prime 15478312159 := by
  apply lucas_primality 15478312159 (12 : ZMod 15478312159)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (29, 1), (79, 1), (375341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (29, 1), (79, 1), (375341, 1)] : List FactorBlock).map factorBlockValue).prod = 15478312159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_79
      · exact prime_eightyOneCA_375341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 15478312159) ^ 7739156079 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (12 : ZMod 15478312159) ^ 5159437386 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (12 : ZMod 15478312159) ^ 533734902 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (12 : ZMod 15478312159) ^ 195928002 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (12 : ZMod 15478312159) ^ 41238 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_15618604627 : Nat.Prime 15618604627 := by
  apply lucas_primality 15618604627 (2 : ZMod 15618604627)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (289233419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (289233419, 1)] : List FactorBlock).map factorBlockValue).prod = 15618604627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_289233419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15618604627) ^ 7809302313 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15618604627) ^ 5206201542 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15618604627) ^ 54 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_19738705873 : Nat.Prime 19738705873 := by
  apply lucas_primality 19738705873 (7 : ZMod 19738705873)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (411223039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (411223039, 1)] : List FactorBlock).map factorBlockValue).prod = 19738705873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_411223039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 19738705873) ^ 9869352936 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 19738705873) ^ 6579568624 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 19738705873) ^ 48 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_20246815859 : Nat.Prime 20246815859 := by
  apply lucas_primality 20246815859 (2 : ZMod 20246815859)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (10123407929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (10123407929, 1)] : List FactorBlock).map factorBlockValue).prod = 20246815859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_10123407929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 20246815859) ^ 10123407929 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20246815859) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_20334088351 : Nat.Prime 20334088351 := by
  apply lucas_primality 20334088351 (6 : ZMod 20334088351)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 2), (5303, 1), (8521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 2), (5303, 1), (8521, 1)] : List FactorBlock).map factorBlockValue).prod = 20334088351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_5303
      · exact prime_eightyOneCA_8521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20334088351) ^ 10167044175 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 20334088351) ^ 6778029450 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 20334088351) ^ 4066817670 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 20334088351) ^ 3834450 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 20334088351) ^ 2386350 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_23630438971 : Nat.Prime 23630438971 := by
  apply lucas_primality 23630438971 (2 : ZMod 23630438971)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (23, 1), (41, 2), (6791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (23, 1), (41, 2), (6791, 1)] : List FactorBlock).map factorBlockValue).prod = 23630438971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_6791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23630438971) ^ 11815219485 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23630438971) ^ 7876812990 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23630438971) ^ 4726087794 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23630438971) ^ 1027410390 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23630438971) ^ 576352170 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23630438971) ^ 3479670 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_26381190683 : Nat.Prime 26381190683 := by
  apply lucas_primality 26381190683 (2 : ZMod 26381190683)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (17, 1), (593, 1), (16993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (17, 1), (593, 1), (16993, 1)] : List FactorBlock).map factorBlockValue).prod = 26381190683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_593
      · exact prime_eightyOneCA_16993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26381190683) ^ 13190595341 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26381190683) ^ 3768741526 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26381190683) ^ 2398290062 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26381190683) ^ 1551834746 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26381190683) ^ 44487674 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26381190683) ^ 1552474 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_33422036749 : Nat.Prime 33422036749 := by
  apply lucas_primality 33422036749 (6 : ZMod 33422036749)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (41, 1), (6469, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (41, 1), (6469, 1), (10501, 1)] : List FactorBlock).map factorBlockValue).prod = 33422036749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_6469
      · exact prime_eightyOneCA_10501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33422036749) ^ 16711018374 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33422036749) ^ 11140678916 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33422036749) ^ 815171628 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33422036749) ^ 5166492 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33422036749) ^ 3182748 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_35464644623 : Nat.Prime 35464644623 := by
  apply lucas_primality 35464644623 (5 : ZMod 35464644623)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (94825253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (94825253, 1)] : List FactorBlock).map factorBlockValue).prod = 35464644623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_94825253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35464644623) ^ 17732322311 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 35464644623) ^ 3224058602 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 35464644623) ^ 2086155566 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 35464644623) ^ 374 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_39125463791 : Nat.Prime 39125463791 := by
  apply lucas_primality 39125463791 (7 : ZMod 39125463791)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (17, 1), (83, 1), (179, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (17, 1), (83, 1), (179, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod = 39125463791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_179
      · exact prime_eightyOneCA_2213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39125463791) ^ 19562731895 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 7825092758 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 5589351970 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 2301497870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 471391130 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 218578010 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39125463791) ^ 17679830 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_39889100257 : Nat.Prime 39889100257 := by
  apply lucas_primality 39889100257 (15 : ZMod 39889100257)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (509, 1), (816329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (509, 1), (816329, 1)] : List FactorBlock).map factorBlockValue).prod = 39889100257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_509
      · exact prime_eightyOneCA_816329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 39889100257) ^ 19944550128 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 39889100257) ^ 13296366752 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 39889100257) ^ 78367584 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 39889100257) ^ 48864 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_42996882989 : Nat.Prime 42996882989 := by
  apply lucas_primality 42996882989 (2 : ZMod 42996882989)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (10749220747, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (10749220747, 1)] : List FactorBlock).map factorBlockValue).prod = 42996882989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_10749220747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 42996882989) ^ 21498441494 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 42996882989) ^ 4 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_46977799907 : Nat.Prime 46977799907 := by
  apply lucas_primality 46977799907 (2 : ZMod 46977799907)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (643, 1), (36530171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (643, 1), (36530171, 1)] : List FactorBlock).map factorBlockValue).prod = 46977799907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_643
      · exact prime_eightyOneCA_36530171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46977799907) ^ 23488899953 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46977799907) ^ 73060342 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46977799907) ^ 1286 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_52762381367 : Nat.Prime 52762381367 := by
  apply lucas_primality 52762381367 (5 : ZMod 52762381367)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (26381190683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (26381190683, 1)] : List FactorBlock).map factorBlockValue).prod = 52762381367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_26381190683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 52762381367) ^ 26381190683 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 52762381367) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_54632410447 : Nat.Prime 54632410447 := by
  apply lucas_primality 54632410447 (3 : ZMod 54632410447)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (61, 1), (149268881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (61, 1), (149268881, 1)] : List FactorBlock).map factorBlockValue).prod = 54632410447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_61
      · exact prime_eightyOneCA_149268881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54632410447) ^ 27316205223 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54632410447) ^ 18210803482 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54632410447) ^ 895613286 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54632410447) ^ 366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_59251292437 : Nat.Prime 59251292437 := by
  apply lucas_primality 59251292437 (2 : ZMod 59251292437)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (397, 1), (1776757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (397, 1), (1776757, 1)] : List FactorBlock).map factorBlockValue).prod = 59251292437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_397
      · exact prime_eightyOneCA_1776757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59251292437) ^ 29625646218 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59251292437) ^ 19750430812 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59251292437) ^ 8464470348 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59251292437) ^ 149247588 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59251292437) ^ 33348 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_59504329541 : Nat.Prime 59504329541 := by
  apply lucas_primality 59504329541 (2 : ZMod 59504329541)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (2975216477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (2975216477, 1)] : List FactorBlock).map factorBlockValue).prod = 59504329541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_2975216477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59504329541) ^ 29752164770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59504329541) ^ 11900865908 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59504329541) ^ 20 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_61247629777 : Nat.Prime 61247629777 := by
  apply lucas_primality 61247629777 (5 : ZMod 61247629777)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (67, 1), (101, 1), (193, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (67, 1), (101, 1), (193, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod = 61247629777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_67
      · exact prime_eightyOneCA_101
      · exact prime_eightyOneCA_193
      · exact prime_eightyOneCA_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 61247629777) ^ 30623814888 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 61247629777) ^ 20415876592 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 61247629777) ^ 914143728 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 61247629777) ^ 606412176 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 61247629777) ^ 317345232 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 61247629777) ^ 62689488 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_68801972893 : Nat.Prime 68801972893 := by
  apply lucas_primality 68801972893 (7 : ZMod 68801972893)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19, 1), (17750767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19, 1), (17750767, 1)] : List FactorBlock).map factorBlockValue).prod = 68801972893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_17750767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 68801972893) ^ 34400986446 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 68801972893) ^ 22933990964 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 68801972893) ^ 4047174876 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 68801972893) ^ 3621156468 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 68801972893) ^ 3876 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_83110087141 : Nat.Prime 83110087141 := by
  apply lucas_primality 83110087141 (6 : ZMod 83110087141)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1385168119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1385168119, 1)] : List FactorBlock).map factorBlockValue).prod = 83110087141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1385168119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 83110087141) ^ 41555043570 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83110087141) ^ 27703362380 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83110087141) ^ 16622017428 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 83110087141) ^ 60 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_86892924529 : Nat.Prime 86892924529 := by
  apply lucas_primality 86892924529 (7 : ZMod 86892924529)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (201141029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (201141029, 1)] : List FactorBlock).map factorBlockValue).prod = 86892924529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_201141029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 86892924529) ^ 43446462264 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 86892924529) ^ 28964308176 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 86892924529) ^ 432 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_103861996583 : Nat.Prime 103861996583 := by
  apply lucas_primality 103861996583 (7 : ZMod 103861996583)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (1790724079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (1790724079, 1)] : List FactorBlock).map factorBlockValue).prod = 103861996583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_1790724079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 103861996583) ^ 51930998291 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 103861996583) ^ 3581448158 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 103861996583) ^ 58 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_110890125161 : Nat.Prime 110890125161 := by
  apply lucas_primality 110890125161 (3 : ZMod 110890125161)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (43, 1), (64471003, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (43, 1), (64471003, 1)] : List FactorBlock).map factorBlockValue).prod = 110890125161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_64471003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110890125161) ^ 55445062580 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 110890125161) ^ 22178025032 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 110890125161) ^ 2578840120 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 110890125161) ^ 1720 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_114880130219 : Nat.Prime 114880130219 := by
  apply lucas_primality 114880130219 (2 : ZMod 114880130219)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (8205723587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (8205723587, 1)] : List FactorBlock).map factorBlockValue).prod = 114880130219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_8205723587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 114880130219) ^ 57440065109 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 114880130219) ^ 16411447174 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 114880130219) ^ 14 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_128188293811 : Nat.Prime 128188293811 := by
  apply lucas_primality 128188293811 (3 : ZMod 128188293811)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (36037, 1), (118571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (36037, 1), (118571, 1)] : List FactorBlock).map factorBlockValue).prod = 128188293811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_36037
      · exact prime_eightyOneCA_118571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128188293811) ^ 64094146905 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 128188293811) ^ 42729431270 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 128188293811) ^ 25637658762 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 128188293811) ^ 3557130 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 128188293811) ^ 1081110 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_154964198047 : Nat.Prime 154964198047 := by
  apply lucas_primality 154964198047 (5 : ZMod 154964198047)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (2459, 1), (214351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (2459, 1), (214351, 1)] : List FactorBlock).map factorBlockValue).prod = 154964198047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_2459
      · exact prime_eightyOneCA_214351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 154964198047) ^ 77482099023 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 154964198047) ^ 51654732682 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 154964198047) ^ 22137742578 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 154964198047) ^ 63019194 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 154964198047) ^ 722946 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_203956379329 : Nat.Prime 203956379329 := by
  apply lucas_primality 203956379329 (7 : ZMod 203956379329)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (13, 1), (2549, 1), (32057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (13, 1), (2549, 1), (32057, 1)] : List FactorBlock).map factorBlockValue).prod = 203956379329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_2549
      · exact prime_eightyOneCA_32057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 203956379329) ^ 101978189664 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 203956379329) ^ 67985459776 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 203956379329) ^ 15688952256 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 203956379329) ^ 80014272 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 203956379329) ^ 6362304 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_243823542847 : Nat.Prime 243823542847 := by
  apply lucas_primality 243823542847 (5 : ZMod 243823542847)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (23, 1), (29, 1), (4686571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (23, 1), (29, 1), (4686571, 1)] : List FactorBlock).map factorBlockValue).prod = 243823542847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_4686571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 243823542847) ^ 121911771423 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 243823542847) ^ 81274514282 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 243823542847) ^ 18755657142 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 243823542847) ^ 10601023602 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 243823542847) ^ 8407708374 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 243823542847) ^ 52026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_299570647349 : Nat.Prime 299570647349 := by
  apply lucas_primality 299570647349 (2 : ZMod 299570647349)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (10698951691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (10698951691, 1)] : List FactorBlock).map factorBlockValue).prod = 299570647349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_10698951691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 299570647349) ^ 149785323674 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 299570647349) ^ 42795806764 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 299570647349) ^ 28 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_306071495791 : Nat.Prime 306071495791 := by
  apply lucas_primality 306071495791 (3 : ZMod 306071495791)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (29, 1), (449, 1), (783533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (29, 1), (449, 1), (783533, 1)] : List FactorBlock).map factorBlockValue).prod = 306071495791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_449
      · exact prime_eightyOneCA_783533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 306071495791) ^ 153035747895 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 306071495791) ^ 102023831930 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 306071495791) ^ 61214299158 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 306071495791) ^ 10554189510 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 306071495791) ^ 681673710 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 306071495791) ^ 390630 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_334220367491 : Nat.Prime 334220367491 := by
  apply lucas_primality 334220367491 (2 : ZMod 334220367491)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (33422036749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (33422036749, 1)] : List FactorBlock).map factorBlockValue).prod = 334220367491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_33422036749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 334220367491) ^ 167110183745 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 334220367491) ^ 66844073498 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 334220367491) ^ 10 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_341557638847 : Nat.Prime 341557638847 := by
  apply lucas_primality 341557638847 (5 : ZMod 341557638847)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (2996119639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (2996119639, 1)] : List FactorBlock).map factorBlockValue).prod = 341557638847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_2996119639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 341557638847) ^ 170778819423 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 341557638847) ^ 113852546282 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 341557638847) ^ 17976717834 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 341557638847) ^ 114 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_376924517509 : Nat.Prime 376924517509 := by
  apply lucas_primality 376924517509 (10 : ZMod 376924517509)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 2), (11, 1), (58275281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 2), (11, 1), (58275281, 1)] : List FactorBlock).map factorBlockValue).prod = 376924517509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_58275281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 376924517509) ^ 188462258754 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 376924517509) ^ 125641505836 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 376924517509) ^ 53846359644 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 376924517509) ^ 34265865228 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 376924517509) ^ 6468 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_400258545061 : Nat.Prime 400258545061 := by
  apply lucas_primality 400258545061 (2 : ZMod 400258545061)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 2), (53, 1), (1040227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 2), (53, 1), (1040227, 1)] : List FactorBlock).map factorBlockValue).prod = 400258545061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_53
      · exact prime_eightyOneCA_1040227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 400258545061) ^ 200129272530 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 400258545061) ^ 133419515020 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 400258545061) ^ 80051709012 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 400258545061) ^ 36387140460 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 400258545061) ^ 7552048020 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 400258545061) ^ 384780 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_420021318403 : Nat.Prime 420021318403 := by
  apply lucas_primality 420021318403 (5 : ZMod 420021318403)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (29, 1), (38316121, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (29, 1), (38316121, 1)] : List FactorBlock).map factorBlockValue).prod = 420021318403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_38316121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 420021318403) ^ 210010659201 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 420021318403) ^ 140007106134 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 420021318403) ^ 60003045486 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 420021318403) ^ 14483493738 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 420021318403) ^ 10962 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_496334400343 : Nat.Prime 496334400343 := by
  apply lucas_primality 496334400343 (3 : ZMod 496334400343)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (149, 1), (50471263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (149, 1), (50471263, 1)] : List FactorBlock).map factorBlockValue).prod = 496334400343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_149
      · exact prime_eightyOneCA_50471263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 496334400343) ^ 248167200171 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 496334400343) ^ 165444800114 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 496334400343) ^ 45121309122 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 496334400343) ^ 3331103358 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 496334400343) ^ 9834 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_587288356583 : Nat.Prime 587288356583 := by
  apply lucas_primality 587288356583 (5 : ZMod 587288356583)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (167, 1), (47522929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (167, 1), (47522929, 1)] : List FactorBlock).map factorBlockValue).prod = 587288356583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_167
      · exact prime_eightyOneCA_47522929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 587288356583) ^ 293644178291 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 587288356583) ^ 15872658286 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 587288356583) ^ 3516696746 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 587288356583) ^ 12358 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_985563678733 : Nat.Prime 985563678733 := by
  apply lucas_primality 985563678733 (2 : ZMod 985563678733)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (34141, 1), (2405621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (34141, 1), (2405621, 1)] : List FactorBlock).map factorBlockValue).prod = 985563678733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_34141
      · exact prime_eightyOneCA_2405621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 985563678733) ^ 492781839366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 985563678733) ^ 328521226244 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 985563678733) ^ 28867452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 985563678733) ^ 409692 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1084556655683 : Nat.Prime 1084556655683 := by
  apply lucas_primality 1084556655683 (2 : ZMod 1084556655683)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (163, 1), (181, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (163, 1), (181, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod = 1084556655683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_59
      · exact prime_eightyOneCA_163
      · exact prime_eightyOneCA_181
      · exact prime_eightyOneCA_311533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1084556655683) ^ 542278327841 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084556655683) ^ 18382316198 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084556655683) ^ 6653721814 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084556655683) ^ 5992025722 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084556655683) ^ 3481354 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1226672264821 : Nat.Prime 1226672264821 := by
  apply lucas_primality 1226672264821 (7 : ZMod 1226672264821)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (463, 1), (44156669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (463, 1), (44156669, 1)] : List FactorBlock).map factorBlockValue).prod = 1226672264821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_463
      · exact prime_eightyOneCA_44156669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1226672264821) ^ 613336132410 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226672264821) ^ 408890754940 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226672264821) ^ 245334452964 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226672264821) ^ 2649400140 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226672264821) ^ 27780 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1250750583211 : Nat.Prime 1250750583211 := by
  apply lucas_primality 1250750583211 (3 : ZMod 1250750583211)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (193, 1), (216019099, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (193, 1), (216019099, 1)] : List FactorBlock).map factorBlockValue).prod = 1250750583211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_193
      · exact prime_eightyOneCA_216019099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1250750583211) ^ 625375291605 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250750583211) ^ 416916861070 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250750583211) ^ 250150116642 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250750583211) ^ 6480572970 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250750583211) ^ 5790 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1501844266723 : Nat.Prime 1501844266723 := by
  apply lucas_primality 1501844266723 (2 : ZMod 1501844266723)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (23, 1), (43, 1), (13913, 1), (18191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (23, 1), (43, 1), (13913, 1), (18191, 1)] : List FactorBlock).map factorBlockValue).prod = 1501844266723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_13913
      · exact prime_eightyOneCA_18191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1501844266723) ^ 750922133361 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501844266723) ^ 500614755574 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501844266723) ^ 65297576814 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501844266723) ^ 34926610854 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501844266723) ^ 107945394 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1501844266723) ^ 82559742 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1603055212393 : Nat.Prime 1603055212393 := by
  apply lucas_primality 1603055212393 (7 : ZMod 1603055212393)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (19, 1), (181, 1), (19422497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (19, 1), (181, 1), (19422497, 1)] : List FactorBlock).map factorBlockValue).prod = 1603055212393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_181
      · exact prime_eightyOneCA_19422497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1603055212393) ^ 801527606196 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603055212393) ^ 534351737464 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603055212393) ^ 84371326968 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603055212393) ^ 8856658632 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1603055212393) ^ 82536 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1673428417981 : Nat.Prime 1673428417981 := by
  apply lucas_primality 1673428417981 (2 : ZMod 1673428417981)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (2535497603, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (2535497603, 1)] : List FactorBlock).map factorBlockValue).prod = 1673428417981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_2535497603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1673428417981) ^ 836714208990 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673428417981) ^ 557809472660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673428417981) ^ 334685683596 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673428417981) ^ 152129856180 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1673428417981) ^ 660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1712135515751 : Nat.Prime 1712135515751 := by
  apply lucas_primality 1712135515751 (11 : ZMod 1712135515751)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (11, 1), (947, 1), (657439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (11, 1), (947, 1), (657439, 1)] : List FactorBlock).map factorBlockValue).prod = 1712135515751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_947
      · exact prime_eightyOneCA_657439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1712135515751) ^ 856067757875 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1712135515751) ^ 342427103150 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1712135515751) ^ 155648683250 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1712135515751) ^ 1807957250 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1712135515751) ^ 2604250 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2581317960887 : Nat.Prime 2581317960887 := by
  apply lucas_primality 2581317960887 (5 : ZMod 2581317960887)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (2963, 1), (62227423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (2963, 1), (62227423, 1)] : List FactorBlock).map factorBlockValue).prod = 2581317960887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_2963
      · exact prime_eightyOneCA_62227423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2581317960887) ^ 1290658980443 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2581317960887) ^ 368759708698 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2581317960887) ^ 871183922 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2581317960887) ^ 41482 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2946868129427 : Nat.Prime 2946868129427 := by
  apply lucas_primality 2946868129427 (2 : ZMod 2946868129427)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (29, 1), (3908313169, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (29, 1), (3908313169, 1)] : List FactorBlock).map factorBlockValue).prod = 2946868129427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_3908313169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2946868129427) ^ 1473434064713 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2946868129427) ^ 226682163802 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2946868129427) ^ 101616142394 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2946868129427) ^ 754 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4770907490689 : Nat.Prime 4770907490689 := by
  apply lucas_primality 4770907490689 (22 : ZMod 4770907490689)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (61, 1), (643, 1), (316759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (61, 1), (643, 1), (316759, 1)] : List FactorBlock).map factorBlockValue).prod = 4770907490689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_61
      · exact prime_eightyOneCA_643
      · exact prime_eightyOneCA_316759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 4770907490689) ^ 2385453745344 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (22 : ZMod 4770907490689) ^ 1590302496896 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (22 : ZMod 4770907490689) ^ 78211598208 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (22 : ZMod 4770907490689) ^ 7419762816 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (22 : ZMod 4770907490689) ^ 15061632 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4920174722171 : Nat.Prime 4920174722171 := by
  apply lucas_primality 4920174722171 (6 : ZMod 4920174722171)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (53611, 1), (9177547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (53611, 1), (9177547, 1)] : List FactorBlock).map factorBlockValue).prod = 4920174722171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_53611
      · exact prime_eightyOneCA_9177547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4920174722171) ^ 2460087361085 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4920174722171) ^ 984034944434 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4920174722171) ^ 91775470 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4920174722171) ^ 536110 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_5040255820837 : Nat.Prime 5040255820837 := by
  apply lucas_primality 5040255820837 (2 : ZMod 5040255820837)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (420021318403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (420021318403, 1)] : List FactorBlock).map factorBlockValue).prod = 5040255820837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_420021318403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5040255820837) ^ 2520127910418 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5040255820837) ^ 1680085273612 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5040255820837) ^ 12 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_5956012804117 : Nat.Prime 5956012804117 := by
  apply lucas_primality 5956012804117 (5 : ZMod 5956012804117)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (496334400343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (496334400343, 1)] : List FactorBlock).map factorBlockValue).prod = 5956012804117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_496334400343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5956012804117) ^ 2978006402058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5956012804117) ^ 1985337601372 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5956012804117) ^ 12 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_6875187759983 : Nat.Prime 6875187759983 := by
  apply lucas_primality 6875187759983 (5 : ZMod 6875187759983)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (110890125161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (110890125161, 1)] : List FactorBlock).map factorBlockValue).prod = 6875187759983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_110890125161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6875187759983) ^ 3437593879991 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6875187759983) ^ 221780250322 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6875187759983) ^ 62 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_7303282321031 : Nat.Prime 7303282321031 := by
  apply lucas_primality 7303282321031 (11 : ZMod 7303282321031)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (157, 1), (4651772179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (157, 1), (4651772179, 1)] : List FactorBlock).map factorBlockValue).prod = 7303282321031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_157
      · exact prime_eightyOneCA_4651772179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7303282321031) ^ 3651641160515 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7303282321031) ^ 1460656464206 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7303282321031) ^ 46517721790 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7303282321031) ^ 1570 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_8001508204717 : Nat.Prime 8001508204717 := by
  apply lucas_primality 8001508204717 (6 : ZMod 8001508204717)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (133403, 1), (384487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (133403, 1), (384487, 1)] : List FactorBlock).map factorBlockValue).prod = 8001508204717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_133403
      · exact prime_eightyOneCA_384487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8001508204717) ^ 4000754102358 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8001508204717) ^ 2667169401572 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8001508204717) ^ 615500631132 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8001508204717) ^ 59979972 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8001508204717) ^ 20810868 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_8267938002733 : Nat.Prime 8267938002733 := by
  apply lucas_primality 8267938002733 (2 : ZMod 8267938002733)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1061, 1), (649382501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1061, 1), (649382501, 1)] : List FactorBlock).map factorBlockValue).prod = 8267938002733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_1061
      · exact prime_eightyOneCA_649382501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8267938002733) ^ 4133969001366 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8267938002733) ^ 2755979334244 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8267938002733) ^ 7792590012 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8267938002733) ^ 12732 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_8285343418493 : Nat.Prime 8285343418493 := by
  apply lucas_primality 8285343418493 (2 : ZMod 8285343418493)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (31, 1), (103, 1), (4831, 1), (19183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (31, 1), (103, 1), (4831, 1), (19183, 1)] : List FactorBlock).map factorBlockValue).prod = 8285343418493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_103
      · exact prime_eightyOneCA_4831
      · exact prime_eightyOneCA_19183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8285343418493) ^ 4142671709246 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8285343418493) ^ 1183620488356 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8285343418493) ^ 267269142532 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8285343418493) ^ 80440227364 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8285343418493) ^ 1715036932 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8285343418493) ^ 431910724 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_9028062687013 : Nat.Prime 9028062687013 := by
  apply lucas_primality 9028062687013 (5 : ZMod 9028062687013)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (307, 1), (2450614193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (307, 1), (2450614193, 1)] : List FactorBlock).map factorBlockValue).prod = 9028062687013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_307
      · exact prime_eightyOneCA_2450614193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9028062687013) ^ 4514031343506 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9028062687013) ^ 3009354229004 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9028062687013) ^ 29407370316 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9028062687013) ^ 3684 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_9196877125847 : Nat.Prime 9196877125847 := by
  apply lucas_primality 9196877125847 (5 : ZMod 9196877125847)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (26399, 1), (174189877, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (26399, 1), (174189877, 1)] : List FactorBlock).map factorBlockValue).prod = 9196877125847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_26399
      · exact prime_eightyOneCA_174189877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9196877125847) ^ 4598438562923 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9196877125847) ^ 348379754 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9196877125847) ^ 52798 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_14052327646109 : Nat.Prime 14052327646109 := by
  apply lucas_primality 14052327646109 (2 : ZMod 14052327646109)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (67, 1), (251, 1), (379, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (67, 1), (251, 1), (379, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod = 14052327646109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_67
      · exact prime_eightyOneCA_251
      · exact prime_eightyOneCA_379
      · exact prime_eightyOneCA_14897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14052327646109) ^ 7026163823054 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14052327646109) ^ 379792639084 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14052327646109) ^ 209736233524 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14052327646109) ^ 55985369108 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14052327646109) ^ 37077381652 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14052327646109) ^ 943299164 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_14997124018601 : Nat.Prime 14997124018601 := by
  apply lucas_primality 14997124018601 (6 : ZMod 14997124018601)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (17, 1), (4363, 1), (1010983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (17, 1), (4363, 1), (1010983, 1)] : List FactorBlock).map factorBlockValue).prod = 14997124018601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_4363
      · exact prime_eightyOneCA_1010983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14997124018601) ^ 7498562009300 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14997124018601) ^ 2999424803720 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14997124018601) ^ 882183765800 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14997124018601) ^ 3437342200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14997124018601) ^ 14834200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_15709006232827 : Nat.Prime 15709006232827 := by
  apply lucas_primality 15709006232827 (2 : ZMod 15709006232827)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (433, 1), (997, 1), (6064771, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (433, 1), (997, 1), (6064771, 1)] : List FactorBlock).map factorBlockValue).prod = 15709006232827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_433
      · exact prime_eightyOneCA_997
      · exact prime_eightyOneCA_6064771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15709006232827) ^ 7854503116413 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15709006232827) ^ 5236335410942 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15709006232827) ^ 36279460122 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15709006232827) ^ 15756275058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15709006232827) ^ 2590206 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_16040498691661 : Nat.Prime 16040498691661 := by
  apply lucas_primality 16040498691661 (7 : ZMod 16040498691661)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (29, 1), (991, 1), (9302399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (29, 1), (991, 1), (9302399, 1)] : List FactorBlock).map factorBlockValue).prod = 16040498691661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_991
      · exact prime_eightyOneCA_9302399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16040498691661) ^ 8020249345830 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16040498691661) ^ 5346832897220 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16040498691661) ^ 3208099738332 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16040498691661) ^ 553120644540 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16040498691661) ^ 16186174260 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 16040498691661) ^ 1724340 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_17535770129749 : Nat.Prime 17535770129749 := by
  apply lucas_primality 17535770129749 (2 : ZMod 17535770129749)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (29, 1), (18973, 1), (204299, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (29, 1), (18973, 1), (204299, 1)] : List FactorBlock).map factorBlockValue).prod = 17535770129749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_18973
      · exact prime_eightyOneCA_204299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17535770129749) ^ 8767885064874 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17535770129749) ^ 5845256709916 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17535770129749) ^ 1348905394596 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17535770129749) ^ 604681728612 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17535770129749) ^ 924248676 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17535770129749) ^ 85833852 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_18961959394633 : Nat.Prime 18961959394633 := by
  apply lucas_primality 18961959394633 (5 : ZMod 18961959394633)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (83, 1), (571, 1), (16670851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (83, 1), (571, 1), (16670851, 1)] : List FactorBlock).map factorBlockValue).prod = 18961959394633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_571
      · exact prime_eightyOneCA_16670851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18961959394633) ^ 9480979697316 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18961959394633) ^ 6320653131544 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18961959394633) ^ 228457342104 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18961959394633) ^ 33208335192 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18961959394633) ^ 1137432 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_20089635416803 : Nat.Prime 20089635416803 := by
  apply lucas_primality 20089635416803 (2 : ZMod 20089635416803)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (149, 1), (2657, 1), (402739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (149, 1), (2657, 1), (402739, 1)] : List FactorBlock).map factorBlockValue).prod = 20089635416803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_149
      · exact prime_eightyOneCA_2657
      · exact prime_eightyOneCA_402739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20089635416803) ^ 10044817708401 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20089635416803) ^ 6696545138934 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20089635416803) ^ 2869947916686 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20089635416803) ^ 134829767898 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20089635416803) ^ 7561021986 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20089635416803) ^ 49882518 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_23974366555751 : Nat.Prime 23974366555751 := by
  apply lucas_primality 23974366555751 (29 : ZMod 23974366555751)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (13, 1), (25969, 1), (284059, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (13, 1), (25969, 1), (284059, 1)] : List FactorBlock).map factorBlockValue).prod = 23974366555751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_25969
      · exact prime_eightyOneCA_284059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 23974366555751) ^ 11987183277875 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (29 : ZMod 23974366555751) ^ 4794873311150 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (29 : ZMod 23974366555751) ^ 1844182042750 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (29 : ZMod 23974366555751) ^ 923191750 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (29 : ZMod 23974366555751) ^ 84399250 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_34073934234961 : Nat.Prime 34073934234961 := by
  apply lucas_primality 34073934234961 (14 : ZMod 34073934234961)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (23, 1), (6172814173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (23, 1), (6172814173, 1)] : List FactorBlock).map factorBlockValue).prod = 34073934234961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_6172814173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 34073934234961) ^ 17036967117480 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (14 : ZMod 34073934234961) ^ 11357978078320 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (14 : ZMod 34073934234961) ^ 6814786846992 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (14 : ZMod 34073934234961) ^ 1481475401520 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (14 : ZMod 34073934234961) ^ 5520 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_39309510729091 : Nat.Prime 39309510729091 := by
  apply lucas_primality 39309510729091 (2 : ZMod 39309510729091)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (389, 1), (481203461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (389, 1), (481203461, 1)] : List FactorBlock).map factorBlockValue).prod = 39309510729091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_389
      · exact prime_eightyOneCA_481203461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39309510729091) ^ 19654755364545 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39309510729091) ^ 13103170243030 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39309510729091) ^ 7861902145818 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39309510729091) ^ 5615644389870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39309510729091) ^ 101052726810 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39309510729091) ^ 81690 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_40665888679573 : Nat.Prime 40665888679573 := by
  apply lucas_primality 40665888679573 (2 : ZMod 40665888679573)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (13, 1), (86892924529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (13, 1), (86892924529, 1)] : List FactorBlock).map factorBlockValue).prod = 40665888679573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_86892924529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40665888679573) ^ 20332944339786 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40665888679573) ^ 13555296226524 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40665888679573) ^ 3128145283044 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40665888679573) ^ 468 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_42284761673977 : Nat.Prime 42284761673977 := by
  apply lucas_primality 42284761673977 (5 : ZMod 42284761673977)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (587288356583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (587288356583, 1)] : List FactorBlock).map factorBlockValue).prod = 42284761673977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_587288356583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42284761673977) ^ 21142380836988 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 42284761673977) ^ 14094920557992 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 42284761673977) ^ 72 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_43681273034797 : Nat.Prime 43681273034797 := by
  apply lucas_primality 43681273034797 (6 : ZMod 43681273034797)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (79817, 1), (15201883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (79817, 1), (15201883, 1)] : List FactorBlock).map factorBlockValue).prod = 43681273034797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_79817
      · exact prime_eightyOneCA_15201883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 43681273034797) ^ 21840636517398 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 43681273034797) ^ 14560424344932 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 43681273034797) ^ 547267788 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 43681273034797) ^ 2873412 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_54168376122079 : Nat.Prime 54168376122079 := by
  apply lucas_primality 54168376122079 (3 : ZMod 54168376122079)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (9028062687013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (9028062687013, 1)] : List FactorBlock).map factorBlockValue).prod = 54168376122079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_9028062687013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54168376122079) ^ 27084188061039 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54168376122079) ^ 18056125374026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54168376122079) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_54836936613023 : Nat.Prime 54836936613023 := by
  apply lucas_primality 54836936613023 (10 : ZMod 54836936613023)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (113, 1), (173, 1), (14243, 1), (98473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (113, 1), (173, 1), (14243, 1), (98473, 1)] : List FactorBlock).map factorBlockValue).prod = 54836936613023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_113
      · exact prime_eightyOneCA_173
      · exact prime_eightyOneCA_14243
      · exact prime_eightyOneCA_98473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 54836936613023) ^ 27418468306511 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 54836936613023) ^ 485282624894 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 54836936613023) ^ 316976512214 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 54836936613023) ^ 3850097354 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 54836936613023) ^ 556872814 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_55729406338129 : Nat.Prime 55729406338129 := by
  apply lucas_primality 55729406338129 (11 : ZMod 55729406338129)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (29, 1), (433, 1), (30820241, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (29, 1), (433, 1), (30820241, 1)] : List FactorBlock).map factorBlockValue).prod = 55729406338129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_433
      · exact prime_eightyOneCA_30820241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 55729406338129) ^ 27864703169064 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 55729406338129) ^ 18576468779376 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 55729406338129) ^ 1921703666832 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 55729406338129) ^ 128705326416 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 55729406338129) ^ 1808208 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_57444624634399 : Nat.Prime 57444624634399 := by
  apply lucas_primality 57444624634399 (3 : ZMod 57444624634399)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (971, 1), (9860045423, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (971, 1), (9860045423, 1)] : List FactorBlock).map factorBlockValue).prod = 57444624634399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_971
      · exact prime_eightyOneCA_9860045423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57444624634399) ^ 28722312317199 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57444624634399) ^ 19148208211466 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57444624634399) ^ 59160272538 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57444624634399) ^ 5826 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_67155794015903 : Nat.Prime 67155794015903 := by
  apply lucas_primality 67155794015903 (5 : ZMod 67155794015903)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3698203, 1), (9079517, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3698203, 1), (9079517, 1)] : List FactorBlock).map factorBlockValue).prod = 67155794015903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3698203
      · exact prime_eightyOneCA_9079517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67155794015903) ^ 33577897007951 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 67155794015903) ^ 18159034 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 67155794015903) ^ 7396406 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_76947610210643 : Nat.Prime 76947610210643 := by
  apply lucas_primality 76947610210643 (2 : ZMod 76947610210643)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (239, 1), (1759, 1), (5209, 1), (17569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (239, 1), (1759, 1), (5209, 1), (17569, 1)] : List FactorBlock).map factorBlockValue).prod = 76947610210643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_239
      · exact prime_eightyOneCA_1759
      · exact prime_eightyOneCA_5209
      · exact prime_eightyOneCA_17569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76947610210643) ^ 38473805105321 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 76947610210643) ^ 321956528078 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 76947610210643) ^ 43745088238 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 76947610210643) ^ 14772050338 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 76947610210643) ^ 4379737618 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_79099672016777 : Nat.Prime 79099672016777 := by
  apply lucas_primality 79099672016777 (3 : ZMod 79099672016777)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (59, 1), (257, 1), (652078019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (59, 1), (257, 1), (652078019, 1)] : List FactorBlock).map factorBlockValue).prod = 79099672016777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_59
      · exact prime_eightyOneCA_257
      · exact prime_eightyOneCA_652078019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 79099672016777) ^ 39549836008388 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 79099672016777) ^ 1340672407064 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 79099672016777) ^ 307780824968 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 79099672016777) ^ 121304 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_85338884579953 : Nat.Prime 85338884579953 := by
  apply lucas_primality 85338884579953 (5 : ZMod 85338884579953)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (17, 1), (53, 1), (307, 1), (6427507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (17, 1), (53, 1), (307, 1), (6427507, 1)] : List FactorBlock).map factorBlockValue).prod = 85338884579953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_53
      · exact prime_eightyOneCA_307
      · exact prime_eightyOneCA_6427507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 85338884579953) ^ 42669442289976 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85338884579953) ^ 28446294859984 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85338884579953) ^ 5019934387056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85338884579953) ^ 1610167633584 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85338884579953) ^ 277976822736 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85338884579953) ^ 13277136 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_115994807858903 : Nat.Prime 115994807858903 := by
  apply lucas_primality 115994807858903 (5 : ZMod 115994807858903)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (8285343418493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (8285343418493, 1)] : List FactorBlock).map factorBlockValue).prod = 115994807858903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_8285343418493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 115994807858903) ^ 57997403929451 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115994807858903) ^ 16570686836986 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115994807858903) ^ 14 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_119981655228559 : Nat.Prime 119981655228559 := by
  apply lucas_primality 119981655228559 (3 : ZMod 119981655228559)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (379, 1), (52762381367, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (379, 1), (52762381367, 1)] : List FactorBlock).map factorBlockValue).prod = 119981655228559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_379
      · exact prime_eightyOneCA_52762381367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119981655228559) ^ 59990827614279 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119981655228559) ^ 39993885076186 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119981655228559) ^ 316574288202 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119981655228559) ^ 2274 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_143618041510571 : Nat.Prime 143618041510571 := by
  apply lucas_primality 143618041510571 (2 : ZMod 143618041510571)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (19, 1), (727, 1), (94520999, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (19, 1), (727, 1), (94520999, 1)] : List FactorBlock).map factorBlockValue).prod = 143618041510571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_727
      · exact prime_eightyOneCA_94520999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 143618041510571) ^ 71809020755285 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 143618041510571) ^ 28723608302114 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 143618041510571) ^ 13056185591870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 143618041510571) ^ 7558844290030 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 143618041510571) ^ 197548887910 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 143618041510571) ^ 1519430 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_149186182379803 : Nat.Prime 149186182379803 := by
  apply lucas_primality 149186182379803 (2 : ZMod 149186182379803)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (83, 1), (299570647349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (83, 1), (299570647349, 1)] : List FactorBlock).map factorBlockValue).prod = 149186182379803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_299570647349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 149186182379803) ^ 74593091189901 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 149186182379803) ^ 49728727459934 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 149186182379803) ^ 1797423884094 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 149186182379803) ^ 498 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_205742558056271 : Nat.Prime 205742558056271 := by
  apply lucas_primality 205742558056271 (11 : ZMod 205742558056271)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (337, 1), (6263, 1), (9747917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (337, 1), (6263, 1), (9747917, 1)] : List FactorBlock).map factorBlockValue).prod = 205742558056271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_337
      · exact prime_eightyOneCA_6263
      · exact prime_eightyOneCA_9747917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 205742558056271) ^ 102871279028135 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 205742558056271) ^ 41148511611254 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 205742558056271) ^ 610512041710 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 205742558056271) ^ 32850480290 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 205742558056271) ^ 21106310 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_229778498537597 : Nat.Prime 229778498537597 := by
  apply lucas_primality 229778498537597 (2 : ZMod 229778498537597)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (57444624634399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (57444624634399, 1)] : List FactorBlock).map factorBlockValue).prod = 229778498537597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_57444624634399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 229778498537597) ^ 114889249268798 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 229778498537597) ^ 4 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_267701562655931 : Nat.Prime 267701562655931 := by
  apply lucas_primality 267701562655931 (2 : ZMod 267701562655931)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (7841, 1), (262625021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (7841, 1), (262625021, 1)] : List FactorBlock).map factorBlockValue).prod = 267701562655931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_7841
      · exact prime_eightyOneCA_262625021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 267701562655931) ^ 133850781327965 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267701562655931) ^ 53540312531186 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267701562655931) ^ 20592427896610 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267701562655931) ^ 34141252730 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 267701562655931) ^ 1019330 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_322693650468439 : Nat.Prime 322693650468439 := by
  apply lucas_primality 322693650468439 (3 : ZMod 322693650468439)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (1250750583211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (1250750583211, 1)] : List FactorBlock).map factorBlockValue).prod = 322693650468439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_1250750583211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 322693650468439) ^ 161346825234219 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 322693650468439) ^ 107564550156146 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 322693650468439) ^ 7504503499266 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 322693650468439) ^ 258 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_333626422112309 : Nat.Prime 333626422112309 := by
  apply lucas_primality 333626422112309 (2 : ZMod 333626422112309)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (19, 1), (137, 1), (233, 1), (10578571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (19, 1), (137, 1), (233, 1), (10578571, 1)] : List FactorBlock).map factorBlockValue).prod = 333626422112309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_137
      · exact prime_eightyOneCA_233
      · exact prime_eightyOneCA_10578571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 333626422112309) ^ 166813211056154 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 333626422112309) ^ 25663570931716 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 333626422112309) ^ 17559285374332 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 333626422112309) ^ 2435229358484 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 333626422112309) ^ 1431873056276 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 333626422112309) ^ 31537948 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_393095107290911 : Nat.Prime 393095107290911 := by
  apply lucas_primality 393095107290911 (7 : ZMod 393095107290911)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (39309510729091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (39309510729091, 1)] : List FactorBlock).map factorBlockValue).prod = 393095107290911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_39309510729091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 393095107290911) ^ 196547553645455 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 393095107290911) ^ 78619021458182 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 393095107290911) ^ 10 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_427958816172919 : Nat.Prime 427958816172919 := by
  apply lucas_primality 427958816172919 (15 : ZMod 427958816172919)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (167, 1), (109589, 1), (3897331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (167, 1), (109589, 1), (3897331, 1)] : List FactorBlock).map factorBlockValue).prod = 427958816172919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_167
      · exact prime_eightyOneCA_109589
      · exact prime_eightyOneCA_3897331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 427958816172919) ^ 213979408086459 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 427958816172919) ^ 142652938724306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 427958816172919) ^ 2562627641754 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 427958816172919) ^ 3905125662 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 427958816172919) ^ 109808178 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_429919250714021 : Nat.Prime 429919250714021 := by
  apply lucas_primality 429919250714021 (2 : ZMod 429919250714021)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (17, 1), (5333, 1), (237102641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (17, 1), (5333, 1), (237102641, 1)] : List FactorBlock).map factorBlockValue).prod = 429919250714021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_5333
      · exact prime_eightyOneCA_237102641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429919250714021) ^ 214959625357010 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 429919250714021) ^ 85983850142804 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 429919250714021) ^ 25289367689060 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 429919250714021) ^ 80614897940 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 429919250714021) ^ 1813220 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_538565301849401 : Nat.Prime 538565301849401 := by
  apply lucas_primality 538565301849401 (15 : ZMod 538565301849401)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (7, 1), (19, 1), (20246815859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (7, 1), (19, 1), (20246815859, 1)] : List FactorBlock).map factorBlockValue).prod = 538565301849401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_20246815859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 538565301849401) ^ 269282650924700 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 538565301849401) ^ 107713060369880 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 538565301849401) ^ 76937900264200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 538565301849401) ^ 28345542202600 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (15 : ZMod 538565301849401) ^ 26600 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_586870574927339 : Nat.Prime 586870574927339 := by
  apply lucas_primality 586870574927339 (2 : ZMod 586870574927339)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (3182033, 1), (7093561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (3182033, 1), (7093561, 1)] : List FactorBlock).map factorBlockValue).prod = 586870574927339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_3182033
      · exact prime_eightyOneCA_7093561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 586870574927339) ^ 293435287463669 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 586870574927339) ^ 45143890379026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 586870574927339) ^ 184432586 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 586870574927339) ^ 82732858 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_669659012139641 : Nat.Prime 669659012139641 := by
  apply lucas_primality 669659012139641 (3 : ZMod 669659012139641)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (22483, 1), (744628177, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (22483, 1), (744628177, 1)] : List FactorBlock).map factorBlockValue).prod = 669659012139641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_22483
      · exact prime_eightyOneCA_744628177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 669659012139641) ^ 334829506069820 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 669659012139641) ^ 133931802427928 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 669659012139641) ^ 29785127080 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 669659012139641) ^ 899320 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_702616382305451 : Nat.Prime 702616382305451 := by
  apply lucas_primality 702616382305451 (6 : ZMod 702616382305451)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (14052327646109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (14052327646109, 1)] : List FactorBlock).map factorBlockValue).prod = 702616382305451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_14052327646109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 702616382305451) ^ 351308191152725 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 702616382305451) ^ 140523276461090 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 702616382305451) ^ 50 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_849114815498737 : Nat.Prime 849114815498737 := by
  apply lucas_primality 849114815498737 (5 : ZMod 849114815498737)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (61, 1), (353, 1), (367, 1), (2238487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (61, 1), (353, 1), (367, 1), (2238487, 1)] : List FactorBlock).map factorBlockValue).prod = 849114815498737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_61
      · exact prime_eightyOneCA_353
      · exact prime_eightyOneCA_367
      · exact prime_eightyOneCA_2238487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 849114815498737) ^ 424557407749368 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 849114815498737) ^ 283038271832912 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 849114815498737) ^ 13919915008176 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 849114815498737) ^ 2405424406512 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 849114815498737) ^ 2313664347408 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 849114815498737) ^ 379325328 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1126085139105679 : Nat.Prime 1126085139105679 := by
  apply lucas_primality 1126085139105679 (7 : ZMod 1126085139105679)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (1226672264821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (1226672264821, 1)] : List FactorBlock).map factorBlockValue).prod = 1126085139105679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_1226672264821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1126085139105679) ^ 563042569552839 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1126085139105679) ^ 375361713035226 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1126085139105679) ^ 66240302300334 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1126085139105679) ^ 918 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1191704274685739 : Nat.Prime 1191704274685739 := by
  apply lucas_primality 1191704274685739 (2 : ZMod 1191704274685739)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (54168376122079, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (54168376122079, 1)] : List FactorBlock).map factorBlockValue).prod = 1191704274685739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_54168376122079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1191704274685739) ^ 595852137342869 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191704274685739) ^ 108336752244158 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191704274685739) ^ 22 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1247855538106759 : Nat.Prime 1247855538106759 := by
  apply lucas_primality 1247855538106759 (6 : ZMod 1247855538106759)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (691, 1), (42996882989, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (691, 1), (42996882989, 1)] : List FactorBlock).map factorBlockValue).prod = 1247855538106759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_691
      · exact prime_eightyOneCA_42996882989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1247855538106759) ^ 623927769053379 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1247855538106759) ^ 415951846035586 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1247855538106759) ^ 178265076872394 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1247855538106759) ^ 1805869085538 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1247855538106759) ^ 29022 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1301927309189219 : Nat.Prime 1301927309189219 := by
  apply lucas_primality 1301927309189219 (2 : ZMod 1301927309189219)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (389, 1), (1673428417981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (389, 1), (1673428417981, 1)] : List FactorBlock).map factorBlockValue).prod = 1301927309189219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_389
      · exact prime_eightyOneCA_1673428417981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1301927309189219) ^ 650963654594609 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301927309189219) ^ 3346856835962 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1301927309189219) ^ 778 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1375352180892421 : Nat.Prime 1375352180892421 := by
  apply lucas_primality 1375352180892421 (10 : ZMod 1375352180892421)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (17, 1), (37, 1), (1913, 1), (19050091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (17, 1), (37, 1), (1913, 1), (19050091, 1)] : List FactorBlock).map factorBlockValue).prod = 1375352180892421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_1913
      · exact prime_eightyOneCA_19050091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1375352180892421) ^ 687676090446210 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 458450726964140 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 275070436178484 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 80903069464260 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 37171680564660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 718950434340 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 1375352180892421) ^ 72196620 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1711835264691677 : Nat.Prime 1711835264691677 := by
  apply lucas_primality 1711835264691677 (2 : ZMod 1711835264691677)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (427958816172919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (427958816172919, 1)] : List FactorBlock).map factorBlockValue).prod = 1711835264691677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_427958816172919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1711835264691677) ^ 855917632345838 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1711835264691677) ^ 4 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_4264575534806519 : Nat.Prime 4264575534806519 := by
  apply lucas_primality 4264575534806519 (7 : ZMod 4264575534806519)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (627611, 1), (91823437, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (627611, 1), (91823437, 1)] : List FactorBlock).map factorBlockValue).prod = 4264575534806519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_627611
      · exact prime_eightyOneCA_91823437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4264575534806519) ^ 2132287767403259 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 4264575534806519) ^ 115258798238014 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 4264575534806519) ^ 6794934338 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 4264575534806519) ^ 46443214 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_5901147445807267 : Nat.Prime 5901147445807267 := by
  apply lucas_primality 5901147445807267 (5 : ZMod 5901147445807267)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (307, 1), (1169767, 1), (2738719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (307, 1), (1169767, 1), (2738719, 1)] : List FactorBlock).map factorBlockValue).prod = 5901147445807267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_307
      · exact prime_eightyOneCA_1169767
      · exact prime_eightyOneCA_2738719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5901147445807267) ^ 2950573722903633 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5901147445807267) ^ 1967049148602422 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5901147445807267) ^ 19221978650838 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5901147445807267) ^ 5044720398 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5901147445807267) ^ 2154710814 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_7188198258915769 : Nat.Prime 7188198258915769 := by
  apply lucas_primality 7188198258915769 (19 : ZMod 7188198258915769)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (73, 1), (17627, 1), (232759567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (73, 1), (17627, 1), (232759567, 1)] : List FactorBlock).map factorBlockValue).prod = 7188198258915769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_73
      · exact prime_eightyOneCA_17627
      · exact prime_eightyOneCA_232759567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 7188198258915769) ^ 3594099129457884 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 7188198258915769) ^ 2396066086305256 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 7188198258915769) ^ 98468469300216 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 7188198258915769) ^ 407794761384 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 7188198258915769) ^ 30882504 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_7406732090025757 : Nat.Prime 7406732090025757 := by
  apply lucas_primality 7406732090025757 (2 : ZMod 7406732090025757)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (205742558056271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (205742558056271, 1)] : List FactorBlock).map factorBlockValue).prod = 7406732090025757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_205742558056271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7406732090025757) ^ 3703366045012878 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7406732090025757) ^ 2468910696675252 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7406732090025757) ^ 36 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_7602918071958823 : Nat.Prime 7602918071958823 := by
  apply lucas_primality 7602918071958823 (5 : ZMod 7602918071958823)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (81131, 1), (15618604627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (81131, 1), (15618604627, 1)] : List FactorBlock).map factorBlockValue).prod = 7602918071958823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_81131
      · exact prime_eightyOneCA_15618604627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7602918071958823) ^ 3801459035979411 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7602918071958823) ^ 2534306023986274 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7602918071958823) ^ 93711627762 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7602918071958823) ^ 486786 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_8677554859340831 : Nat.Prime 8677554859340831 := by
  apply lucas_primality 8677554859340831 (7 : ZMod 8677554859340831)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (1686389, 1), (514564247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (1686389, 1), (514564247, 1)] : List FactorBlock).map factorBlockValue).prod = 8677554859340831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1686389
      · exact prime_eightyOneCA_514564247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8677554859340831) ^ 4338777429670415 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8677554859340831) ^ 1735510971868166 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8677554859340831) ^ 5145642470 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8677554859340831) ^ 16863890 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10647088821026393 : Nat.Prime 10647088821026393 := by
  apply lucas_primality 10647088821026393 (5 : ZMod 10647088821026393)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (414643, 1), (458530799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (414643, 1), (458530799, 1)] : List FactorBlock).map factorBlockValue).prod = 10647088821026393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_414643
      · exact prime_eightyOneCA_458530799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10647088821026393) ^ 5323544410513196 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10647088821026393) ^ 1521012688718056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10647088821026393) ^ 25677724744 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10647088821026393) ^ 23220008 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_11555714404150363 : Nat.Prime 11555714404150363 := by
  apply lucas_primality 11555714404150363 (2 : ZMod 11555714404150363)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (14039057, 1), (45728437, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (14039057, 1), (45728437, 1)] : List FactorBlock).map factorBlockValue).prod = 11555714404150363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_14039057
      · exact prime_eightyOneCA_45728437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11555714404150363) ^ 5777857202075181 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11555714404150363) ^ 3851904801383454 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11555714404150363) ^ 823111866 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11555714404150363) ^ 252703026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_15381888979776967 : Nat.Prime 15381888979776967 := by
  apply lucas_primality 15381888979776967 (5 : ZMod 15381888979776967)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (569, 1), (1501844266723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (569, 1), (1501844266723, 1)] : List FactorBlock).map factorBlockValue).prod = 15381888979776967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_569
      · exact prime_eightyOneCA_1501844266723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15381888979776967) ^ 7690944489888483 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15381888979776967) ^ 5127296326592322 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15381888979776967) ^ 27033196801014 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15381888979776967) ^ 10242 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_24476257666626037 : Nat.Prime 24476257666626037 := by
  apply lucas_primality 24476257666626037 (6 : ZMod 24476257666626037)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (119981655228559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (119981655228559, 1)] : List FactorBlock).map factorBlockValue).prod = 24476257666626037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_119981655228559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24476257666626037) ^ 12238128833313018 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24476257666626037) ^ 8158752555542012 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24476257666626037) ^ 1439779862742708 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24476257666626037) ^ 204 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_24649420543196233 : Nat.Prime 24649420543196233 := by
  apply lucas_primality 24649420543196233 (10 : ZMod 24649420543196233)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (439, 1), (334220367491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (439, 1), (334220367491, 1)] : List FactorBlock).map factorBlockValue).prod = 24649420543196233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_439
      · exact prime_eightyOneCA_334220367491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 24649420543196233) ^ 12324710271598116 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 24649420543196233) ^ 8216473514398744 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 24649420543196233) ^ 3521345791885176 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 24649420543196233) ^ 56149021738488 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 24649420543196233) ^ 73752 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_31203261366513391 : Nat.Prime 31203261366513391 := by
  apply lucas_primality 31203261366513391 (3 : ZMod 31203261366513391)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (863, 1), (5217421921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (863, 1), (5217421921, 1)] : List FactorBlock).map factorBlockValue).prod = 31203261366513391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_863
      · exact prime_eightyOneCA_5217421921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31203261366513391) ^ 15601630683256695 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 10401087122171130 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 6240652273302678 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 4457608766644770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 2836660124228490 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 36156733912530 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31203261366513391) ^ 5980590 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_48685798391859331 : Nat.Prime 48685798391859331 := by
  apply lucas_primality 48685798391859331 (2 : ZMod 48685798391859331)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (11171, 1), (44071, 1), (253567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (11171, 1), (44071, 1), (253567, 1)] : List FactorBlock).map factorBlockValue).prod = 48685798391859331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_11171
      · exact prime_eightyOneCA_44071
      · exact prime_eightyOneCA_253567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48685798391859331) ^ 24342899195929665 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 16228599463953110 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 9737159678371866 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 3745061414758410 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 4358230990230 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 1104712813230 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 48685798391859331) ^ 192003684990 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_63266200321051367 : Nat.Prime 63266200321051367 := by
  apply lucas_primality 63266200321051367 (5 : ZMod 63266200321051367)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (1375352180892421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (1375352180892421, 1)] : List FactorBlock).map factorBlockValue).prod = 63266200321051367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_1375352180892421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 63266200321051367) ^ 31633100160525683 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63266200321051367) ^ 2750704361784842 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 63266200321051367) ^ 46 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_84594182524579667 : Nat.Prime 84594182524579667 := by
  apply lucas_primality 84594182524579667 (2 : ZMod 84594182524579667)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (43, 1), (811, 1), (39125463791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (43, 1), (811, 1), (39125463791, 1)] : List FactorBlock).map factorBlockValue).prod = 84594182524579667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_811
      · exact prime_eightyOneCA_39125463791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84594182524579667) ^ 42297091262289833 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84594182524579667) ^ 2728844597567086 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84594182524579667) ^ 1967306570339062 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84594182524579667) ^ 104308486466806 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 84594182524579667) ^ 2162126 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_86493787469467421 : Nat.Prime 86493787469467421 := by
  apply lucas_primality 86493787469467421 (2 : ZMod 86493787469467421)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 2), (19, 1), (773, 1), (9109, 1), (659713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 2), (19, 1), (773, 1), (9109, 1), (659713, 1)] : List FactorBlock).map factorBlockValue).prod = 86493787469467421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_773
      · exact prime_eightyOneCA_9109
      · exact prime_eightyOneCA_659713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 86493787469467421) ^ 43246893734733710 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 17298757493893484 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 12356255352781060 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 4552304603656180 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 111893644850540 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 9495420734380 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 86493787469467421) ^ 131108205340 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_92139974206861409 : Nat.Prime 92139974206861409 := by
  apply lucas_primality 92139974206861409 (3 : ZMod 92139974206861409)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (650081, 1), (4429254499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (650081, 1), (4429254499, 1)] : List FactorBlock).map factorBlockValue).prod = 92139974206861409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_650081
      · exact prime_eightyOneCA_4429254499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 92139974206861409) ^ 46069987103430704 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 92139974206861409) ^ 141736143968 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 92139974206861409) ^ 20802592 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_118507713440412113 : Nat.Prime 118507713440412113 := by
  apply lucas_primality 118507713440412113 (3 : ZMod 118507713440412113)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7406732090025757, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7406732090025757, 1)] : List FactorBlock).map factorBlockValue).prod = 118507713440412113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7406732090025757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 118507713440412113) ^ 59253856720206056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 118507713440412113) ^ 16 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_150113462513011381 : Nat.Prime 150113462513011381 := by
  apply lucas_primality 150113462513011381 (6 : ZMod 150113462513011381)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (283, 1), (2946868129427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (283, 1), (2946868129427, 1)] : List FactorBlock).map factorBlockValue).prod = 150113462513011381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_283
      · exact prime_eightyOneCA_2946868129427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 150113462513011381) ^ 75056731256505690 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 150113462513011381) ^ 50037820837670460 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 150113462513011381) ^ 30022692502602276 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 150113462513011381) ^ 530436263296860 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 150113462513011381) ^ 50940 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_165886135276764443 : Nat.Prime 165886135276764443 := by
  apply lucas_primality 165886135276764443 (2 : ZMod 165886135276764443)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (211, 1), (393095107290911, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (211, 1), (393095107290911, 1)] : List FactorBlock).map factorBlockValue).prod = 165886135276764443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_211
      · exact prime_eightyOneCA_393095107290911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 165886135276764443) ^ 82943067638382221 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 165886135276764443) ^ 786190214581822 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 165886135276764443) ^ 422 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_183282585855149591 : Nat.Prime 183282585855149591 := by
  apply lucas_primality 183282585855149591 (13 : ZMod 183282585855149591)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (434963, 1), (593486083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (434963, 1), (593486083, 1)] : List FactorBlock).map factorBlockValue).prod = 183282585855149591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_71
      · exact prime_eightyOneCA_434963
      · exact prime_eightyOneCA_593486083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 183282585855149591) ^ 91641292927574795 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 183282585855149591) ^ 36656517171029918 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 183282585855149591) ^ 2581444871199290 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 183282585855149591) ^ 421375118930 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 183282585855149591) ^ 308823730 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_201269551249641533 : Nat.Prime 201269551249641533 := by
  apply lucas_primality 201269551249641533 (3 : ZMod 201269551249641533)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (7188198258915769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (7188198258915769, 1)] : List FactorBlock).map factorBlockValue).prod = 201269551249641533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_7188198258915769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 201269551249641533) ^ 100634775624820766 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 201269551249641533) ^ 28752793035663076 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 201269551249641533) ^ 28 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_244134477860115979 : Nat.Prime 244134477860115979 := by
  apply lucas_primality 244134477860115979 (2 : ZMod 244134477860115979)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (19, 1), (29, 1), (79, 1), (103861996583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (19, 1), (29, 1), (79, 1), (103861996583, 1)] : List FactorBlock).map factorBlockValue).prod = 244134477860115979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_79
      · exact prime_eightyOneCA_103861996583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 244134477860115979) ^ 122067238930057989 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 244134477860115979) ^ 81378159286705326 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 244134477860115979) ^ 12849183045269262 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 244134477860115979) ^ 8418430271038482 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 244134477860115979) ^ 3090309846330582 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 244134477860115979) ^ 2350566 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_252626406753190117 : Nat.Prime 252626406753190117 := by
  apply lucas_primality 252626406753190117 (2 : ZMod 252626406753190117)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (23, 1), (41, 1), (1689847, 1), (13211083, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (23, 1), (41, 1), (1689847, 1), (13211083, 1)] : List FactorBlock).map factorBlockValue).prod = 252626406753190117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_41
      · exact prime_eightyOneCA_1689847
      · exact prime_eightyOneCA_13211083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252626406753190117) ^ 126313203376595058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 252626406753190117) ^ 84208802251063372 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 252626406753190117) ^ 10983756815356092 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 252626406753190117) ^ 6161619676907076 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 252626406753190117) ^ 149496615228 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 252626406753190117) ^ 19122308652 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_266092089228323483 : Nat.Prime 266092089228323483 := by
  apply lucas_primality 266092089228323483 (2 : ZMod 266092089228323483)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (37, 1), (115994807858903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (37, 1), (115994807858903, 1)] : List FactorBlock).map factorBlockValue).prod = 266092089228323483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_115994807858903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 266092089228323483) ^ 133046044614161741 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 266092089228323483) ^ 8583615781558822 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 266092089228323483) ^ 7191678087251986 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 266092089228323483) ^ 2294 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_345343159445273537 : Nat.Prime 345343159445273537 := by
  apply lucas_primality 345343159445273537 (3 : ZMod 345343159445273537)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (43, 1), (149, 1), (3389, 1), (248510413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (43, 1), (149, 1), (3389, 1), (248510413, 1)] : List FactorBlock).map factorBlockValue).prod = 345343159445273537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_149
      · exact prime_eightyOneCA_3389
      · exact prime_eightyOneCA_248510413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 345343159445273537) ^ 172671579722636768 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 345343159445273537) ^ 8031236266169152 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 345343159445273537) ^ 2317739325136064 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 345343159445273537) ^ 101901197829824 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 345343159445273537) ^ 1389652672 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_356386789554468301 : Nat.Prime 356386789554468301 := by
  apply lucas_primality 356386789554468301 (2 : ZMod 356386789554468301)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 2), (83, 1), (4770907490689, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 2), (83, 1), (4770907490689, 1)] : List FactorBlock).map factorBlockValue).prod = 356386789554468301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_83
      · exact prime_eightyOneCA_4770907490689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 356386789554468301) ^ 178193394777234150 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 356386789554468301) ^ 118795596518156100 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 356386789554468301) ^ 71277357910893660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 356386789554468301) ^ 4293816741620100 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 356386789554468301) ^ 74700 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_385750849816466531 : Nat.Prime 385750849816466531 := by
  apply lucas_primality 385750849816466531 (2 : ZMod 385750849816466531)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11, 1), (127, 1), (521, 1), (1979, 1), (3319, 1), (8069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11, 1), (127, 1), (521, 1), (1979, 1), (3319, 1), (8069, 1)] : List FactorBlock).map factorBlockValue).prod = 385750849816466531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_127
      · exact prime_eightyOneCA_521
      · exact prime_eightyOneCA_1979
      · exact prime_eightyOneCA_3319
      · exact prime_eightyOneCA_8069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 385750849816466531) ^ 192875424908233265 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 77150169963293306 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 35068259074224230 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 3037408266271390 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 740404702142930 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 194922107032070 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 116225022541870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 385750849816466531) ^ 47806524949370 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_414515324343003503 : Nat.Prime 414515324343003503 := by
  apply lucas_primality 414515324343003503 (5 : ZMod 414515324343003503)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3719, 1), (55729406338129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3719, 1), (55729406338129, 1)] : List FactorBlock).map factorBlockValue).prod = 414515324343003503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3719
      · exact prime_eightyOneCA_55729406338129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 414515324343003503) ^ 207257662171501751 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 414515324343003503) ^ 111458812676258 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 414515324343003503) ^ 7438 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_598891846828749953 : Nat.Prime 598891846828749953 := by
  apply lucas_primality 598891846828749953 (3 : ZMod 598891846828749953)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (17, 1), (43, 1), (2803, 1), (2283483913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (17, 1), (43, 1), (2803, 1), (2283483913, 1)] : List FactorBlock).map factorBlockValue).prod = 598891846828749953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_43
      · exact prime_eightyOneCA_2803
      · exact prime_eightyOneCA_2283483913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 598891846828749953) ^ 299445923414374976 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 598891846828749953) ^ 35228932166397056 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 598891846828749953) ^ 13927717368110464 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 598891846828749953) ^ 213661022771584 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 598891846828749953) ^ 262271104 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_676345868197466167 : Nat.Prime 676345868197466167 := by
  apply lucas_primality 676345868197466167 (3 : ZMod 676345868197466167)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7, 1), (163, 1), (701, 1), (46977799907, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7, 1), (163, 1), (701, 1), (46977799907, 1)] : List FactorBlock).map factorBlockValue).prod = 676345868197466167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_163
      · exact prime_eightyOneCA_701
      · exact prime_eightyOneCA_46977799907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 676345868197466167) ^ 338172934098733083 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 676345868197466167) ^ 225448622732488722 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 676345868197466167) ^ 96620838313923738 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 676345868197466167) ^ 4149361154585682 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 676345868197466167) ^ 964830054489966 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 676345868197466167) ^ 14397138 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_781153159830006659 : Nat.Prime 781153159830006659 := by
  apply lucas_primality 781153159830006659 (2 : ZMod 781153159830006659)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1459, 1), (267701562655931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1459, 1), (267701562655931, 1)] : List FactorBlock).map factorBlockValue).prod = 781153159830006659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1459
      · exact prime_eightyOneCA_267701562655931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 781153159830006659) ^ 390576579915003329 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 781153159830006659) ^ 535403125311862 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 781153159830006659) ^ 2918 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_955264919796660257 : Nat.Prime 955264919796660257 := by
  apply lucas_primality 955264919796660257 (3 : ZMod 955264919796660257)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (7, 1), (4264575534806519, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (7, 1), (4264575534806519, 1)] : List FactorBlock).map factorBlockValue).prod = 955264919796660257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_4264575534806519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 955264919796660257) ^ 477632459898330128 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 955264919796660257) ^ 136466417113808608 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 955264919796660257) ^ 224 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1163923014415161787 : Nat.Prime 1163923014415161787 := by
  apply lucas_primality 1163923014415161787 (5 : ZMod 1163923014415161787)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1301927309189219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1301927309189219, 1)] : List FactorBlock).map factorBlockValue).prod = 1163923014415161787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_149
      · exact prime_eightyOneCA_1301927309189219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1163923014415161787) ^ 581961507207580893 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163923014415161787) ^ 387974338138387262 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163923014415161787) ^ 7811563855135314 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1163923014415161787) ^ 894 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2242405362567176999 : Nat.Prime 2242405362567176999 := by
  apply lucas_primality 2242405362567176999 (11 : ZMod 2242405362567176999)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (134033, 1), (268789, 1), (31121527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (134033, 1), (268789, 1), (31121527, 1)] : List FactorBlock).map factorBlockValue).prod = 2242405362567176999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_134033
      · exact prime_eightyOneCA_268789
      · exact prime_eightyOneCA_31121527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2242405362567176999) ^ 1121202681283588499 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 2242405362567176999) ^ 16730248241606 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 2242405362567176999) ^ 8342623256782 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 2242405362567176999) ^ 72053192074 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2754092380280141587 : Nat.Prime 2754092380280141587 := by
  apply lucas_primality 2754092380280141587 (2 : ZMod 2754092380280141587)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (829, 1), (79099672016777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (829, 1), (79099672016777, 1)] : List FactorBlock).map factorBlockValue).prod = 2754092380280141587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_829
      · exact prime_eightyOneCA_79099672016777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2754092380280141587) ^ 1377046190140070793 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2754092380280141587) ^ 918030793426713862 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2754092380280141587) ^ 393441768611448798 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2754092380280141587) ^ 3322186224704634 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2754092380280141587) ^ 34818 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_10152455735961304351 : Nat.Prime 10152455735961304351 := by
  apply lucas_primality 10152455735961304351 (6 : ZMod 10152455735961304351)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (13, 1), (227, 1), (2423, 1), (37717, 1), (250969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (13, 1), (227, 1), (2423, 1), (37717, 1), (250969, 1)] : List FactorBlock).map factorBlockValue).prod = 10152455735961304351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_227
      · exact prime_eightyOneCA_2423
      · exact prime_eightyOneCA_37717
      · exact prime_eightyOneCA_250969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10152455735961304351) ^ 5076227867980652175 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 3384151911987101450 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 2030491147192260870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 780958133535484950 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 44724474607759050 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 4190035384218450 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 269174529680550 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (6 : ZMod 10152455735961304351) ^ 40453027011150 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_30721373602872632003 : Nat.Prime 30721373602872632003 := by
  apply lucas_primality 30721373602872632003 (2 : ZMod 30721373602872632003)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (137, 1), (5901147445807267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (137, 1), (5901147445807267, 1)] : List FactorBlock).map factorBlockValue).prod = 30721373602872632003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_137
      · exact prime_eightyOneCA_5901147445807267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30721373602872632003) ^ 15360686801436316001 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30721373602872632003) ^ 1616914400151191158 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30721373602872632003) ^ 224243602940676146 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30721373602872632003) ^ 5206 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_31194904476292068521 : Nat.Prime 31194904476292068521 := by
  apply lucas_primality 31194904476292068521 (3 : ZMod 31194904476292068521)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (1303, 1), (303539, 1), (1971808589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (1303, 1), (303539, 1), (1971808589, 1)] : List FactorBlock).map factorBlockValue).prod = 31194904476292068521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1303
      · exact prime_eightyOneCA_303539
      · exact prime_eightyOneCA_1971808589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31194904476292068521) ^ 15597452238146034260 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31194904476292068521) ^ 6238980895258413704 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31194904476292068521) ^ 23940832291858840 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31194904476292068521) ^ 102770663658680 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31194904476292068521) ^ 15820452680 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_74509778596938162671 : Nat.Prime 74509778596938162671 := by
  apply lucas_primality 74509778596938162671 (7 : ZMod 74509778596938162671)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (1083749, 1), (6875187759983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (1083749, 1), (6875187759983, 1)] : List FactorBlock).map factorBlockValue).prod = 74509778596938162671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_1083749
      · exact prime_eightyOneCA_6875187759983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 74509778596938162671) ^ 37254889298469081335 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 74509778596938162671) ^ 14901955719387632534 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 74509778596938162671) ^ 68751877599830 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 74509778596938162671) ^ 10837490 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_163758041346975105601 : Nat.Prime 163758041346975105601 := by
  apply lucas_primality 163758041346975105601 (17 : ZMod 163758041346975105601)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (5, 2), (19, 1), (38669, 1), (15478312159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (5, 2), (19, 1), (38669, 1), (15478312159, 1)] : List FactorBlock).map factorBlockValue).prod = 163758041346975105601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_38669
      · exact prime_eightyOneCA_15478312159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 163758041346975105601) ^ 81879020673487552800 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (17 : ZMod 163758041346975105601) ^ 54586013782325035200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (17 : ZMod 163758041346975105601) ^ 32751608269395021120 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (17 : ZMod 163758041346975105601) ^ 8618844281419742400 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (17 : ZMod 163758041346975105601) ^ 4234866206702400 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (17 : ZMod 163758041346975105601) ^ 10579838400 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_240325325188407616237 : Nat.Prime 240325325188407616237 := by
  apply lucas_primality 240325325188407616237 (2 : ZMod 240325325188407616237)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2177599, 1), (9196877125847, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2177599, 1), (9196877125847, 1)] : List FactorBlock).map factorBlockValue).prod = 240325325188407616237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_2177599
      · exact prime_eightyOneCA_9196877125847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240325325188407616237) ^ 120162662594203808118 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240325325188407616237) ^ 80108441729469205412 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240325325188407616237) ^ 110362525510164 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 240325325188407616237) ^ 26131188 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_478574376453306096479 : Nat.Prime 478574376453306096479 := by
  apply lucas_primality 478574376453306096479 (31 : ZMod 478574376453306096479)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1453, 1), (389579, 1), (554011, 1), (763027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1453, 1), (389579, 1), (554011, 1), (763027, 1)] : List FactorBlock).map factorBlockValue).prod = 478574376453306096479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1453
      · exact prime_eightyOneCA_389579
      · exact prime_eightyOneCA_554011
      · exact prime_eightyOneCA_763027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 478574376453306096479) ^ 239287188226653048239 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (31 : ZMod 478574376453306096479) ^ 329369839265867926 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (31 : ZMod 478574376453306096479) ^ 1228439870869082 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (31 : ZMod 478574376453306096479) ^ 863835513109498 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (31 : ZMod 478574376453306096479) ^ 627205035278314 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_566016883099236105073 : Nat.Prime 566016883099236105073 := by
  apply lucas_primality 566016883099236105073 (5 : ZMod 566016883099236105073)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (1614619, 1), (7303282321031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (1614619, 1), (7303282321031, 1)] : List FactorBlock).map factorBlockValue).prod = 566016883099236105073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_1614619
      · exact prime_eightyOneCA_7303282321031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 566016883099236105073) ^ 283008441549618052536 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 566016883099236105073) ^ 188672294366412035024 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 566016883099236105073) ^ 350557551409488 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 566016883099236105073) ^ 77501712 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_733769055943529042119 : Nat.Prime 733769055943529042119 := by
  apply lucas_primality 733769055943529042119 (3 : ZMod 733769055943529042119)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (19, 1), (3547, 1), (14997124018601, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (19, 1), (3547, 1), (14997124018601, 1)] : List FactorBlock).map factorBlockValue).prod = 733769055943529042119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_3547
      · exact prime_eightyOneCA_14997124018601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 733769055943529042119) ^ 366884527971764521059 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 733769055943529042119) ^ 244589685314509680706 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 733769055943529042119) ^ 66706277813048094738 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 733769055943529042119) ^ 38619423997027844322 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 733769055943529042119) ^ 206870328712582194 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 733769055943529042119) ^ 48927318 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_961301300753630464949 : Nat.Prime 961301300753630464949 := by
  apply lucas_primality 961301300753630464949 (2 : ZMod 961301300753630464949)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (240325325188407616237, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (240325325188407616237, 1)] : List FactorBlock).map factorBlockValue).prod = 961301300753630464949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_240325325188407616237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 961301300753630464949) ^ 480650650376815232474 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 961301300753630464949) ^ 4 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1608662474934321932443 : Nat.Prime 1608662474934321932443 := by
  apply lucas_primality 1608662474934321932443 (3 : ZMod 1608662474934321932443)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (3433, 1), (8677554859340831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (3433, 1), (8677554859340831, 1)] : List FactorBlock).map factorBlockValue).prod = 1608662474934321932443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_3433
      · exact prime_eightyOneCA_8677554859340831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1608662474934321932443) ^ 804331237467160966221 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1608662474934321932443) ^ 536220824978107310814 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1608662474934321932443) ^ 468587962404404874 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1608662474934321932443) ^ 185382 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1955980771742697346499 : Nat.Prime 1955980771742697346499 := by
  apply lucas_primality 1955980771742697346499 (2 : ZMod 1955980771742697346499)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (71, 1), (598891846828749953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (71, 1), (598891846828749953, 1)] : List FactorBlock).map factorBlockValue).prod = 1955980771742697346499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_71
      · exact prime_eightyOneCA_598891846828749953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1955980771742697346499) ^ 977990385871348673249 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955980771742697346499) ^ 85042642249682493326 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955980771742697346499) ^ 27549024954122497838 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1955980771742697346499) ^ 3266 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_3726108152830988627567 : Nat.Prime 3726108152830988627567 := by
  apply lucas_primality 3726108152830988627567 (5 : ZMod 3726108152830988627567)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1493, 1), (16217, 1), (76947610210643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1493, 1), (16217, 1), (76947610210643, 1)] : List FactorBlock).map factorBlockValue).prod = 3726108152830988627567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1493
      · exact prime_eightyOneCA_16217
      · exact prime_eightyOneCA_76947610210643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3726108152830988627567) ^ 1863054076415494313783 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3726108152830988627567) ^ 2495718789571995062 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3726108152830988627567) ^ 229765564088979998 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3726108152830988627567) ^ 48423962 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_3950407983529393335317 : Nat.Prime 3950407983529393335317 := by
  apply lucas_primality 3950407983529393335317 (2 : ZMod 3950407983529393335317)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1549, 1), (2617, 1), (3541, 1), (68801972893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1549, 1), (2617, 1), (3541, 1), (68801972893, 1)] : List FactorBlock).map factorBlockValue).prod = 3950407983529393335317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1549
      · exact prime_eightyOneCA_2617
      · exact prime_eightyOneCA_3541
      · exact prime_eightyOneCA_68801972893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3950407983529393335317) ^ 1975203991764696667658 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3950407983529393335317) ^ 2550295663995734884 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3950407983529393335317) ^ 1509517762143444148 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3950407983529393335317) ^ 1115619311925838276 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3950407983529393335317) ^ 57417074212 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_6187344206886779371777 : Nat.Prime 6187344206886779371777 := by
  apply lucas_primality 6187344206886779371777 (10 : ZMod 6187344206886779371777)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (11, 1), (244134477860115979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (11, 1), (244134477860115979, 1)] : List FactorBlock).map factorBlockValue).prod = 6187344206886779371777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_244134477860115979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6187344206886779371777) ^ 3093672103443389685888 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6187344206886779371777) ^ 2062448068962259790592 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6187344206886779371777) ^ 562485836989707215616 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6187344206886779371777) ^ 25344 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_9703343596879059328843 : Nat.Prime 9703343596879059328843 := by
  apply lucas_primality 9703343596879059328843 (2 : ZMod 9703343596879059328843)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (9749, 1), (165886135276764443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (9749, 1), (165886135276764443, 1)] : List FactorBlock).map factorBlockValue).prod = 9703343596879059328843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_9749
      · exact prime_eightyOneCA_165886135276764443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9703343596879059328843) ^ 4851671798439529664421 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703343596879059328843) ^ 3234447865626353109614 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703343596879059328843) ^ 995316811660586658 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703343596879059328843) ^ 58494 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_13613592381613219707407 : Nat.Prime 13613592381613219707407 := by
  apply lucas_primality 13613592381613219707407 (5 : ZMod 13613592381613219707407)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59251292437, 1), (114880130219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59251292437, 1), (114880130219, 1)] : List FactorBlock).map factorBlockValue).prod = 13613592381613219707407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_59251292437
      · exact prime_eightyOneCA_114880130219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13613592381613219707407) ^ 6806796190806609853703 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13613592381613219707407) ^ 229760260438 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13613592381613219707407) ^ 118502584874 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_14239274052301573943651 : Nat.Prime 14239274052301573943651 := by
  apply lucas_primality 14239274052301573943651 (2 : ZMod 14239274052301573943651)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (127, 1), (2242405362567176999, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (127, 1), (2242405362567176999, 1)] : List FactorBlock).map factorBlockValue).prod = 14239274052301573943651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_127
      · exact prime_eightyOneCA_2242405362567176999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14239274052301573943651) ^ 7119637026150786971825 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14239274052301573943651) ^ 2847854810460314788730 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14239274052301573943651) ^ 112120268128358849950 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14239274052301573943651) ^ 6350 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_20760553665896184691799 : Nat.Prime 20760553665896184691799 := by
  apply lucas_primality 20760553665896184691799 (19 : ZMod 20760553665896184691799)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (10723, 1), (186041, 1), (400258545061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (10723, 1), (186041, 1), (400258545061, 1)] : List FactorBlock).map factorBlockValue).prod = 20760553665896184691799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_10723
      · exact prime_eightyOneCA_186041
      · exact prime_eightyOneCA_400258545061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 20760553665896184691799) ^ 10380276832948092345899 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 20760553665896184691799) ^ 1596965666607398822446 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 20760553665896184691799) ^ 1936076999524031026 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 20760553665896184691799) ^ 111591281845916678 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (19 : ZMod 20760553665896184691799) ^ 51867858718 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_27285429576085638157021 : Nat.Prime 27285429576085638157021 := by
  apply lucas_primality 27285429576085638157021 (7 : ZMod 27285429576085638157021)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (971, 1), (24649420543196233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (971, 1), (24649420543196233, 1)] : List FactorBlock).map factorBlockValue).prod = 27285429576085638157021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_971
      · exact prime_eightyOneCA_24649420543196233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27285429576085638157021) ^ 13642714788042819078510 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27285429576085638157021) ^ 9095143192028546052340 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27285429576085638157021) ^ 5457085915217127631404 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27285429576085638157021) ^ 1436075240846612534580 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27285429576085638157021) ^ 28100339419243705620 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27285429576085638157021) ^ 1106940 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_30087985058476634014483 : Nat.Prime 30087985058476634014483 := by
  apply lucas_primality 30087985058476634014483 (2 : ZMod 30087985058476634014483)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (103, 1), (562193, 1), (919313, 1), (94201061, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (103, 1), (562193, 1), (919313, 1), (94201061, 1)] : List FactorBlock).map factorBlockValue).prod = 30087985058476634014483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_103
      · exact prime_eightyOneCA_562193
      · exact prime_eightyOneCA_919313
      · exact prime_eightyOneCA_94201061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30087985058476634014483) ^ 15043992529238317007241 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30087985058476634014483) ^ 10029328352825544671494 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30087985058476634014483) ^ 292116359791035281694 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30087985058476634014483) ^ 53518960674495474 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30087985058476634014483) ^ 32728771439625714 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30087985058476634014483) ^ 319401764046762 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_36514930142412232523149 : Nat.Prime 36514930142412232523149 := by
  apply lucas_primality 36514930142412232523149 (2 : ZMod 36514930142412232523149)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (113, 1), (863, 1), (31203261366513391, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (113, 1), (863, 1), (31203261366513391, 1)] : List FactorBlock).map factorBlockValue).prod = 36514930142412232523149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_113
      · exact prime_eightyOneCA_863
      · exact prime_eightyOneCA_31203261366513391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36514930142412232523149) ^ 18257465071206116261574 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36514930142412232523149) ^ 12171643380804077507716 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36514930142412232523149) ^ 323140974711612677196 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36514930142412232523149) ^ 42311622412992158196 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36514930142412232523149) ^ 1170228 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_36724121080838951894377 : Nat.Prime 36724121080838951894377 := by
  apply lucas_primality 36724121080838951894377 (10 : ZMod 36724121080838951894377)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (17, 1), (73, 1), (191, 1), (586870574927339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (17, 1), (73, 1), (191, 1), (586870574927339, 1)] : List FactorBlock).map factorBlockValue).prod = 36724121080838951894377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_73
      · exact prime_eightyOneCA_191
      · exact prime_eightyOneCA_586870574927339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 36724121080838951894377) ^ 18362060540419475947188 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 12241373693612983964792 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 3338556461894450172216 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 2160242416519938346728 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 503070151792314409512 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 192272885239994512536 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (10 : ZMod 36724121080838951894377) ^ 62576184 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_68930890044648349182247 : Nat.Prime 68930890044648349182247 := by
  apply lucas_primality 68930890044648349182247 (21 : ZMod 68930890044648349182247)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1979, 1), (3593, 1), (538565301849401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1979, 1), (3593, 1), (538565301849401, 1)] : List FactorBlock).map factorBlockValue).prod = 68930890044648349182247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_1979
      · exact prime_eightyOneCA_3593
      · exact prime_eightyOneCA_538565301849401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 68930890044648349182247) ^ 34465445022324174591123 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (21 : ZMod 68930890044648349182247) ^ 22976963348216116394082 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (21 : ZMod 68930890044648349182247) ^ 34831172331808160274 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (21 : ZMod 68930890044648349182247) ^ 19184773182479362422 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (21 : ZMod 68930890044648349182247) ^ 127989846 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_85435644313809443661907 : Nat.Prime 85435644313809443661907 := by
  apply lucas_primality 85435644313809443661907 (2 : ZMod 85435644313809443661907)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (14239274052301573943651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (14239274052301573943651, 1)] : List FactorBlock).map factorBlockValue).prod = 85435644313809443661907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_14239274052301573943651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85435644313809443661907) ^ 42717822156904721830953 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85435644313809443661907) ^ 28478548104603147887302 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 85435644313809443661907) ^ 6 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_122689716172021257302261 : Nat.Prime 122689716172021257302261 := by
  apply lucas_primality 122689716172021257302261 (2 : ZMod 122689716172021257302261)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (2459, 1), (356386789554468301, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (2459, 1), (356386789554468301, 1)] : List FactorBlock).map factorBlockValue).prod = 122689716172021257302261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_2459
      · exact prime_eightyOneCA_356386789554468301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122689716172021257302261) ^ 61344858086010628651130 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 122689716172021257302261) ^ 24537943234404251460452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 122689716172021257302261) ^ 17527102310288751043180 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 122689716172021257302261) ^ 49894150537625562140 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 122689716172021257302261) ^ 344260 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_135156261625777813628617 : Nat.Prime 135156261625777813628617 := by
  apply lucas_primality 135156261625777813628617 (5 : ZMod 135156261625777813628617)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (23, 1), (709, 1), (345343159445273537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (23, 1), (709, 1), (345343159445273537, 1)] : List FactorBlock).map factorBlockValue).prod = 135156261625777813628617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_23
      · exact prime_eightyOneCA_709
      · exact prime_eightyOneCA_345343159445273537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 135156261625777813628617) ^ 67578130812888906814308 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135156261625777813628617) ^ 45052087208592604542872 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135156261625777813628617) ^ 5876359201120774505592 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135156261625777813628617) ^ 190629424013790992424 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135156261625777813628617) ^ 391368 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_174935959001077072433137 : Nat.Prime 174935959001077072433137 := by
  apply lucas_primality 174935959001077072433137 (5 : ZMod 174935959001077072433137)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (59504329541, 1), (61247629777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (59504329541, 1), (61247629777, 1)] : List FactorBlock).map factorBlockValue).prod = 174935959001077072433137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_59504329541
      · exact prime_eightyOneCA_61247629777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 174935959001077072433137) ^ 87467979500538536216568 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 174935959001077072433137) ^ 58311986333692357477712 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 174935959001077072433137) ^ 2939886229296 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 174935959001077072433137) ^ 2856207817968 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_206312407603127772850391 : Nat.Prime 206312407603127772850391 := by
  apply lucas_primality 206312407603127772850391 (11 : ZMod 206312407603127772850391)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (81667, 1), (252626406753190117, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (81667, 1), (252626406753190117, 1)] : List FactorBlock).map factorBlockValue).prod = 206312407603127772850391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_81667
      · exact prime_eightyOneCA_252626406753190117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 206312407603127772850391) ^ 103156203801563886425195 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 206312407603127772850391) ^ 41262481520625554570078 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 206312407603127772850391) ^ 2526264067531901170 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 206312407603127772850391) ^ 816670 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_245907771666538989311069 : Nat.Prime 245907771666538989311069 := by
  apply lucas_primality 245907771666538989311069 (2 : ZMod 245907771666538989311069)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (518759, 1), (118507713440412113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (518759, 1), (118507713440412113, 1)] : List FactorBlock).map factorBlockValue).prod = 245907771666538989311069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_518759
      · exact prime_eightyOneCA_118507713440412113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 245907771666538989311069) ^ 122953885833269494655534 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 245907771666538989311069) ^ 474030853761648452 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 245907771666538989311069) ^ 2075036 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_440531495764730345973541 : Nat.Prime 440531495764730345973541 := by
  apply lucas_primality 440531495764730345973541 (13 : ZMod 440531495764730345973541)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (2643757, 1), (5040255820837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (2643757, 1), (5040255820837, 1)] : List FactorBlock).map factorBlockValue).prod = 440531495764730345973541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_19
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_2643757
      · exact prime_eightyOneCA_5040255820837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 440531495764730345973541) ^ 220265747882365172986770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 146843831921576781991180 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 88106299152946069194708 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 23185868198143702419660 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 15190741233266563654260 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 166630857436871220 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 440531495764730345973541) ^ 87402606420 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1326494502407831951413853 : Nat.Prime 1326494502407831951413853 := by
  apply lucas_primality 1326494502407831951413853 (2 : ZMod 1326494502407831951413853)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (89, 1), (3726108152830988627567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (89, 1), (3726108152830988627567, 1)] : List FactorBlock).map factorBlockValue).prod = 1326494502407831951413853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_89
      · exact prime_eightyOneCA_3726108152830988627567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1326494502407831951413853) ^ 663247251203915975706926 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1326494502407831951413853) ^ 14904432611323954510268 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1326494502407831951413853) ^ 356 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1781416701310129137943343 : Nat.Prime 1781416701310129137943343 := by
  apply lucas_primality 1781416701310129137943343 (5 : ZMod 1781416701310129137943343)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1048984583, 1), (849114815498737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1048984583, 1), (849114815498737, 1)] : List FactorBlock).map factorBlockValue).prod = 1781416701310129137943343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1048984583
      · exact prime_eightyOneCA_849114815498737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1781416701310129137943343) ^ 890708350655064568971671 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1781416701310129137943343) ^ 1698229630997474 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1781416701310129137943343) ^ 2097969166 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2452458963642916719637889 : Nat.Prime 2452458963642916719637889 := by
  apply lucas_primality 2452458963642916719637889 (3 : ZMod 2452458963642916719637889)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (7, 1), (4087333, 1), (669659012139641, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (7, 1), (4087333, 1), (669659012139641, 1)] : List FactorBlock).map factorBlockValue).prod = 2452458963642916719637889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_4087333
      · exact prime_eightyOneCA_669659012139641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2452458963642916719637889) ^ 1226229481821458359818944 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2452458963642916719637889) ^ 350351280520416674233984 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2452458963642916719637889) ^ 600014474877118336 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2452458963642916719637889) ^ 3662250368 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_2636881284586519042553633 : Nat.Prime 2636881284586519042553633 := by
  apply lucas_primality 2636881284586519042553633 (3 : ZMod 2636881284586519042553633)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (73176119, 1), (1126085139105679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (73176119, 1), (1126085139105679, 1)] : List FactorBlock).map factorBlockValue).prod = 2636881284586519042553633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_73176119
      · exact prime_eightyOneCA_1126085139105679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2636881284586519042553633) ^ 1318440642293259521276816 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2636881284586519042553633) ^ 36034724451381728 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2636881284586519042553633) ^ 2341635808 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_23047802072762602182531959 : Nat.Prime 23047802072762602182531959 := by
  apply lucas_primality 23047802072762602182531959 (13 : ZMod 23047802072762602182531959)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (470819567, 1), (24476257666626037, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (470819567, 1), (24476257666626037, 1)] : List FactorBlock).map factorBlockValue).prod = 23047802072762602182531959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_470819567
      · exact prime_eightyOneCA_24476257666626037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 23047802072762602182531959) ^ 11523901036381301091265979 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 23047802072762602182531959) ^ 48952515333252074 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (13 : ZMod 23047802072762602182531959) ^ 941639134 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_59186413851871824516947027 : Nat.Prime 59186413851871824516947027 := by
  apply lucas_primality 59186413851871824516947027 (2 : ZMod 59186413851871824516947027)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (13901, 1), (163758041346975105601, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (13901, 1), (163758041346975105601, 1)] : List FactorBlock).map factorBlockValue).prod = 59186413851871824516947027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_13901
      · exact prime_eightyOneCA_163758041346975105601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59186413851871824516947027) ^ 29593206925935912258473513 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59186413851871824516947027) ^ 4552801065528601885919002 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59186413851871824516947027) ^ 4257709075021352745626 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 59186413851871824516947027) ^ 361426 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_69494642679483753315254201 : Nat.Prime 69494642679483753315254201 := by
  apply lucas_primality 69494642679483753315254201 (3 : ZMod 69494642679483753315254201)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (61, 1), (829, 1), (286609, 1), (23974366555751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (61, 1), (829, 1), (286609, 1), (23974366555751, 1)] : List FactorBlock).map factorBlockValue).prod = 69494642679483753315254201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_61
      · exact prime_eightyOneCA_829
      · exact prime_eightyOneCA_286609
      · exact prime_eightyOneCA_23974366555751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69494642679483753315254201) ^ 34747321339741876657627100 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 69494642679483753315254201) ^ 13898928535896750663050840 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 69494642679483753315254201) ^ 1139256437368586119922200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 69494642679483753315254201) ^ 83829484534962307979800 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 69494642679483753315254201) ^ 242471948471554463800 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 69494642679483753315254201) ^ 2898706104200 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_84671633609485952315137303 : Nat.Prime 84671633609485952315137303 := by
  apply lucas_primality 84671633609485952315137303 (3 : ZMod 84671633609485952315137303)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (31, 1), (71, 1), (73, 1), (93563, 1), (85338884579953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (31, 1), (71, 1), (73, 1), (93563, 1), (85338884579953, 1)] : List FactorBlock).map factorBlockValue).prod = 84671633609485952315137303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_31
      · exact prime_eightyOneCA_71
      · exact prime_eightyOneCA_73
      · exact prime_eightyOneCA_93563
      · exact prime_eightyOneCA_85338884579953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 84671633609485952315137303) ^ 42335816804742976157568651 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 28223877869828650771712434 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 7697421237225995665012482 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 2731343019660837171456042 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 1192558219851914821339962 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 1159885391910766470070374 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 904969203739576032354 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 84671633609485952315137303) ^ 992181161334 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_138989285358967506630508403 : Nat.Prime 138989285358967506630508403 := by
  apply lucas_primality 138989285358967506630508403 (2 : ZMod 138989285358967506630508403)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (69494642679483753315254201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (69494642679483753315254201, 1)] : List FactorBlock).map factorBlockValue).prod = 138989285358967506630508403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_69494642679483753315254201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 138989285358967506630508403) ^ 69494642679483753315254201 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 138989285358967506630508403) ^ 2 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_193071809702275427557298971 : Nat.Prime 193071809702275427557298971 := by
  apply lucas_primality 193071809702275427557298971 (11 : ZMod 193071809702275427557298971)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (197, 1), (1022773, 1), (10647088821026393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (197, 1), (1022773, 1), (10647088821026393, 1)] : List FactorBlock).map factorBlockValue).prod = 193071809702275427557298971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_197
      · exact prime_eightyOneCA_1022773
      · exact prime_eightyOneCA_10647088821026393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 193071809702275427557298971) ^ 96535904851137713778649485 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 193071809702275427557298971) ^ 64357269900758475852432990 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 193071809702275427557298971) ^ 38614361940455085511459794 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 193071809702275427557298971) ^ 980059947727286434301010 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 193071809702275427557298971) ^ 188772884796797947890 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 193071809702275427557298971) ^ 18133765290 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_195435954310874718506980183 : Nat.Prime 195435954310874718506980183 := by
  apply lucas_primality 195435954310874718506980183 (5 : ZMod 195435954310874718506980183)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (241, 1), (135156261625777813628617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (241, 1), (135156261625777813628617, 1)] : List FactorBlock).map factorBlockValue).prod = 195435954310874718506980183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_241
      · exact prime_eightyOneCA_135156261625777813628617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 195435954310874718506980183) ^ 97717977155437359253490091 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 195435954310874718506980183) ^ 65145318103624906168993394 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 195435954310874718506980183) ^ 810937569754666881771702 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 195435954310874718506980183) ^ 1446 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_338387341386320183987350847 : Nat.Prime 338387341386320183987350847 := by
  apply lucas_primality 338387341386320183987350847 (5 : ZMod 338387341386320183987350847)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (263, 1), (29429, 1), (194687, 1), (16040498691661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (263, 1), (29429, 1), (194687, 1), (16040498691661, 1)] : List FactorBlock).map factorBlockValue).prod = 338387341386320183987350847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_263
      · exact prime_eightyOneCA_29429
      · exact prime_eightyOneCA_194687
      · exact prime_eightyOneCA_16040498691661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 338387341386320183987350847) ^ 169193670693160091993675423 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 338387341386320183987350847) ^ 48341048769474311998192978 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 338387341386320183987350847) ^ 1286643883598175604514642 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 338387341386320183987350847) ^ 11498431526260497603974 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 338387341386320183987350847) ^ 1738109588140554757058 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 338387341386320183987350847) ^ 21095811788086 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_349502254059593474702263831 : Nat.Prime 349502254059593474702263831 := by
  apply lucas_primality 349502254059593474702263831 (11 : ZMod 349502254059593474702263831)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (79, 1), (213659, 1), (44726819, 1), (107913653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (79, 1), (213659, 1), (44726819, 1), (107913653, 1)] : List FactorBlock).map factorBlockValue).prod = 349502254059593474702263831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_13
      · exact prime_eightyOneCA_79
      · exact prime_eightyOneCA_213659
      · exact prime_eightyOneCA_44726819
      · exact prime_eightyOneCA_107913653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 349502254059593474702263831) ^ 174751127029796737351131915 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 116500751353197824900754610 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 69900450811918694940452766 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 31772932187235770427478530 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 26884788773814882669404910 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 4424079165311309806357770 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 1635794673098692190370 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 7814154055078083570 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (11 : ZMod 349502254059593474702263831) ^ 3238721369756554110 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_449594448884171887645165679 : Nat.Prime 449594448884171887645165679 := by
  apply lucas_primality 449594448884171887645165679 (7 : ZMod 449594448884171887645165679)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (173, 1), (1013, 1), (241393, 1), (143618041510571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (173, 1), (1013, 1), (241393, 1), (143618041510571, 1)] : List FactorBlock).map factorBlockValue).prod = 449594448884171887645165679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_37
      · exact prime_eightyOneCA_173
      · exact prime_eightyOneCA_1013
      · exact prime_eightyOneCA_241393
      · exact prime_eightyOneCA_143618041510571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 449594448884171887645165679) ^ 224797224442085943822582839 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 449594448884171887645165679) ^ 12151201321193834801220694 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 449594448884171887645165679) ^ 2598811843261109177139686 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 449594448884171887645165679) ^ 443824727427612919689206 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 449594448884171887645165679) ^ 1862499943594768231246 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (7 : ZMod 449594448884171887645165679) ^ 3130487257418 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_474077314912517881526833117 : Nat.Prime 474077314912517881526833117 := by
  apply lucas_primality 474077314912517881526833117 (2 : ZMod 474077314912517881526833117)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (29, 1), (7069, 1), (10331, 1), (1538909, 1), (1731643981, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (29, 1), (7069, 1), (10331, 1), (1538909, 1), (1731643981, 1)] : List FactorBlock).map factorBlockValue).prod = 474077314912517881526833117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_29
      · exact prime_eightyOneCA_7069
      · exact prime_eightyOneCA_10331
      · exact prime_eightyOneCA_1538909
      · exact prime_eightyOneCA_1731643981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 474077314912517881526833117) ^ 237038657456258940763416558 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 158025771637505960508944372 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 67725330701788268789547588 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 16347493617673030397477004 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 67064268625338503540364 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 45888811820009474545236 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 308060655251556707724 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 474077314912517881526833117) ^ 273772969567765836 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_784947685346955836626395817 : Nat.Prime 784947685346955836626395817 := by
  apply lucas_primality 784947685346955836626395817 (5 : ZMod 784947685346955836626395817)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (11, 1), (17, 1), (103, 1), (566016883099236105073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (11, 1), (17, 1), (103, 1), (566016883099236105073, 1)] : List FactorBlock).map factorBlockValue).prod = 784947685346955836626395817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_11
      · exact prime_eightyOneCA_17
      · exact prime_eightyOneCA_103
      · exact prime_eightyOneCA_566016883099236105073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 784947685346955836626395817) ^ 392473842673477918313197908 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 784947685346955836626395817) ^ 261649228448985278875465272 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 784947685346955836626395817) ^ 71358880486086894238763256 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 784947685346955836626395817) ^ 46173393255703284507435048 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 784947685346955836626395817) ^ 7620851314048114918702872 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 784947685346955836626395817) ^ 1386792 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_1276848234831048160912270529 : Nat.Prime 1276848234831048160912270529 := by
  apply lucas_primality 1276848234831048160912270529 (3 : ZMod 1276848234831048160912270529)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (107, 1), (359, 1), (2687, 1), (73259, 1), (376924517509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (107, 1), (359, 1), (2687, 1), (73259, 1), (376924517509, 1)] : List FactorBlock).map factorBlockValue).prod = 1276848234831048160912270529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_7
      · exact prime_eightyOneCA_107
      · exact prime_eightyOneCA_359
      · exact prime_eightyOneCA_2687
      · exact prime_eightyOneCA_73259
      · exact prime_eightyOneCA_376924517509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1276848234831048160912270529) ^ 638424117415524080456135264 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 182406890690149737273181504 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 11933161073187365989834304 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 3556680319863643902262592 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 475194728258670696282944 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 17429233743718152867392 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1276848234831048160912270529) ^ 3387543594323392 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_15960602935388102011403381611 : Nat.Prime 15960602935388102011403381611 := by
  apply lucas_primality 15960602935388102011403381611 (2 : ZMod 15960602935388102011403381611)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (10927623977, 1), (48685798391859331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (10927623977, 1), (48685798391859331, 1)] : List FactorBlock).map factorBlockValue).prod = 15960602935388102011403381611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_5
      · exact prime_eightyOneCA_10927623977
      · exact prime_eightyOneCA_48685798391859331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15960602935388102011403381611) ^ 7980301467694051005701690805 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15960602935388102011403381611) ^ 5320200978462700670467793870 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15960602935388102011403381611) ^ 3192120587077620402280676322 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15960602935388102011403381611) ^ 1460573951755779930 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15960602935388102011403381611) ^ 327828719310 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_31921205870776204022806763233 : Nat.Prime 31921205870776204022806763233 := by
  apply lucas_primality 31921205870776204022806763233 (5 : ZMod 31921205870776204022806763233)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (17535770129749, 1), (18961959394633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (17535770129749, 1), (18961959394633, 1)] : List FactorBlock).map factorBlockValue).prod = 31921205870776204022806763233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_3
      · exact prime_eightyOneCA_17535770129749
      · exact prime_eightyOneCA_18961959394633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31921205870776204022806763233) ^ 15960602935388102011403381616 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776204022806763233) ^ 10640401956925401340935587744 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776204022806763233) ^ 1820348101884768 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31921205870776204022806763233) ^ 1683433932455904 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide

private theorem prime_eightyOneCA_95763617612328612068420289653 : Nat.Prime 95763617612328612068420289653 := by
  apply lucas_primality 95763617612328612068420289653 (2 : ZMod 95763617612328612068420289653)
  · rw [← eightyOneCAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1249, 1), (664669, 1), (3939805151, 1), (7319778623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1249, 1), (664669, 1), (3939805151, 1), (7319778623, 1)] : List FactorBlock).map factorBlockValue).prod = 95763617612328612068420289653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyOneCA_2
      · exact prime_eightyOneCA_1249
      · exact prime_eightyOneCA_664669
      · exact prime_eightyOneCA_3939805151
      · exact prime_eightyOneCA_7319778623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95763617612328612068420289653) ^ 47881808806164306034210144826 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95763617612328612068420289653) ^ 76672231875363180198895348 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95763617612328612068420289653) ^ 144077153609283135016708 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95763617612328612068420289653) ^ 24306688768103651852 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95763617612328612068420289653) ^ 13082857084150454924 ≠ 1
      rw [← eightyOneCAFastPow_eq_pow]
      decide


/-! ## Exact totients used by the selected window -/

private theorem phi_eightyOneCA_95763617612328612068420289600 : Nat.totient 95763617612328612068420289600 = 21615513929709748473914818560 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (7, 1), (107, 1), (359, 1), (2687, 1), (73259, 1), (376924517509, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_7, prime_eightyOneCA_107, prime_eightyOneCA_359, prime_eightyOneCA_2687, prime_eightyOneCA_73259, prime_eightyOneCA_376924517509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289601 : Nat.totient 95763617612328612068420289601 = 95092535303450627166589995600 := by
  rw [← show ((([(151, 1), (2579, 1), (245907771666538989311069, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_151, prime_eightyOneCA_2579, prime_eightyOneCA_245907771666538989311069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289602 : Nat.totient 95763617612328612068420289602 = 41853896921603480736643806528 := by
  rw [← show ((([(2, 1), (13, 1), (19, 1), (2269, 1), (85435644313809443661907, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_13, prime_eightyOneCA_19, prime_eightyOneCA_2269, prime_eightyOneCA_85435644313809443661907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289603 : Nat.totient 95763617612328612068420289603 = 59894119439222029378986995712 := by
  rw [← show ((([(3, 1), (17, 1), (313, 1), (87943, 1), (356219, 1), (1691219, 1), (113231647, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_17, prime_eightyOneCA_313, prime_eightyOneCA_87943, prime_eightyOneCA_356219, prime_eightyOneCA_1691219, prime_eightyOneCA_113231647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289604 : Nat.totient 95763617612328612068420289604 = 46800575049606558424447057920 := by
  rw [← show ((([(2, 2), (59, 1), (179, 1), (13877, 1), (24481, 1), (32717, 1), (203956379329, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_59, prime_eightyOneCA_179, prime_eightyOneCA_13877, prime_eightyOneCA_24481, prime_eightyOneCA_32717, prime_eightyOneCA_203956379329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289605 : Nat.totient 95763617612328612068420289605 = 76523204493385379504984448000 := by
  rw [← show ((([(5, 1), (1201, 1), (3709, 1), (23459, 1), (183282585855149591, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_1201, prime_eightyOneCA_3709, prime_eightyOneCA_23459, prime_eightyOneCA_183282585855149591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289606 : Nat.totient 95763617612328612068420289606 = 30820474608633824735209538880 := by
  rw [← show ((([(2, 1), (3, 2), (29, 1), (1222110283, 1), (150113462513011381, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_29, prime_eightyOneCA_1222110283, prime_eightyOneCA_150113462513011381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289607 : Nat.totient 95763617612328612068420289607 = 74552176741785373028590755840 := by
  rw [← show ((([(7, 1), (11, 1), (1567, 1), (3517, 1), (11432725553, 1), (19738705873, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_7, prime_eightyOneCA_11, prime_eightyOneCA_1567, prime_eightyOneCA_3517, prime_eightyOneCA_11432725553, prime_eightyOneCA_19738705873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289608 : Nat.totient 95763617612328612068420289608 = 47758719299499415073258327232 := by
  rw [← show ((([(2, 3), (389, 1), (2000558627, 1), (15381888979776967, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_389, prime_eightyOneCA_2000558627, prime_eightyOneCA_15381888979776967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289609 : Nat.totient 95763617612328612068420289609 = 63842408524227458176929974880 := by
  rw [← show ((([(3, 1), (19843321, 1), (1608662474934321932443, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_19843321, prime_eightyOneCA_1608662474934321932443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289610 : Nat.totient 95763617612328612068420289610 = 38052563509174169603218222080 := by
  rw [← show ((([(2, 1), (5, 1), (157, 1), (4391, 1), (164209, 1), (84594182524579667, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_157, prime_eightyOneCA_4391, prime_eightyOneCA_164209, prime_eightyOneCA_84594182524579667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289611 : Nat.totient 95763617612328612068420289611 = 95763491273757973652424364320 := by
  rw [← show ((([(757997, 1), (128188293811, 1), (985563678733, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_757997, prime_eightyOneCA_128188293811, prime_eightyOneCA_985563678733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289612 : Nat.totient 95763617612328612068420289612 = 31921059811055634373875796416 := by
  rw [← show ((([(2, 2), (3, 1), (218549, 1), (36514930142412232523149, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_218549, prime_eightyOneCA_36514930142412232523149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289613 : Nat.totient 95763617612328612068420289613 = 93969879852167143485798009600 := by
  rw [← show ((([(61, 1), (421, 1), (1456099, 1), (2361269, 1), (1084556655683, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_61, prime_eightyOneCA_421, prime_eightyOneCA_1456099, prime_eightyOneCA_2361269, prime_eightyOneCA_1084556655683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289614 : Nat.totient 95763617612328612068420289614 = 40266571263711516770788883232 := by
  rw [← show ((([(2, 1), (7, 1), (53, 1), (65983, 1), (1955980771742697346499, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_7, prime_eightyOneCA_53, prime_eightyOneCA_65983, prime_eightyOneCA_1955980771742697346499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289615 : Nat.totient 95763617612328612068420289615 = 44577220171539916488435793920 := by
  rw [← show ((([(3, 2), (5, 1), (13, 1), (23, 1), (89, 1), (3889, 1), (67184023, 1), (306071495791, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_13, prime_eightyOneCA_23, prime_eightyOneCA_89, prime_eightyOneCA_3889, prime_eightyOneCA_67184023, prime_eightyOneCA_306071495791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289616 : Nat.totient 95763617612328612068420289616 = 46337234328546102613751752800 := by
  rw [← show ((([(2, 4), (31, 1), (193071809702275427557298971, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_31, prime_eightyOneCA_193071809702275427557298971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289617 : Nat.totient 95763617612328612068420289617 = 95763616651027311314690205936 := by
  rw [← show ((([(99618733, 1), (961301300753630464949, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_99618733, prime_eightyOneCA_961301300753630464949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289618 : Nat.totient 95763617612328612068420289618 = 29011170884898700241802374400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (5923, 1), (9181, 1), (610843, 1), (43681273034797, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_11, prime_eightyOneCA_5923, prime_eightyOneCA_9181, prime_eightyOneCA_610843, prime_eightyOneCA_43681273034797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289619 : Nat.totient 95763617612328612068420289619 = 95345418887800713746600174400 := by
  rw [← show ((([(229, 1), (5612441, 1), (74509778596938162671, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_229, prime_eightyOneCA_5612441, prime_eightyOneCA_74509778596938162671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289620 : Nat.totient 95763617612328612068420289620 = 35988824846489182471623720960 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (569, 1), (83110087141, 1), (5956012804117, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_17, prime_eightyOneCA_569, prime_eightyOneCA_83110087141, prime_eightyOneCA_5956012804117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289621 : Nat.totient 95763617612328612068420289621 = 49964798438486793351484968960 := by
  rw [← show ((([(3, 1), (7, 2), (19, 1), (41, 1), (83, 1), (14897, 1), (676345868197466167, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_7, prime_eightyOneCA_19, prime_eightyOneCA_41, prime_eightyOneCA_83, prime_eightyOneCA_14897, prime_eightyOneCA_676345868197466167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289622 : Nat.totient 95763617612328612068420289622 = 47881488069137541513045054592 := by
  rw [← show ((([(2, 1), (174569, 1), (1030793, 1), (266092089228323483, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_174569, prime_eightyOneCA_1030793, prime_eightyOneCA_266092089228323483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289623 : Nat.totient 95763617612328612068420289623 = 95756988886340388398391812184 := by
  rw [← show ((([(14447, 1), (871851583, 1), (7602918071958823, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_14447, prime_eightyOneCA_871851583, prime_eightyOneCA_7602918071958823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289624 : Nat.totient 95763617612328612068420289624 = 31921205664438981313312071168 := by
  rw [← show ((([(2, 3), (3, 4), (154704059, 1), (955264919796660257, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_154704059, prime_eightyOneCA_955264919796660257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289625 : Nat.totient 95763617612328612068420289625 = 76609676988097011430195200000 := by
  rw [← show ((([(5, 3), (99809, 1), (170701, 1), (184469633, 1), (243758561, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_99809, prime_eightyOneCA_170701, prime_eightyOneCA_184469633, prime_eightyOneCA_243758561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289626 : Nat.totient 95763617612328612068420289626 = 47818543211648888715125996544 := by
  rw [← show ((([(2, 1), (823, 1), (9403, 1), (6187344206886779371777, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_823, prime_eightyOneCA_9403, prime_eightyOneCA_6187344206886779371777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289627 : Nat.totient 95763617612328612068420289627 = 62943222843784064270323194920 := by
  rw [← show ((([(3, 1), (71, 1), (449594448884171887645165679, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_71, prime_eightyOneCA_449594448884171887645165679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289628 : Nat.totient 95763617612328612068420289628 = 37884435572533154886364140288 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (523997, 1), (194504143, 1), (2581317960887, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_7, prime_eightyOneCA_13, prime_eightyOneCA_523997, prime_eightyOneCA_194504143, prime_eightyOneCA_2581317960887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289629 : Nat.totient 95763617612328612068420289629 = 87044569248001932651776968240 := by
  rw [← show ((([(11, 1), (6563, 1), (1326494502407831951413853, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_11, prime_eightyOneCA_6563, prime_eightyOneCA_1326494502407831951413853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289630 : Nat.totient 95763617612328612068420289630 = 24943081657422396429560624256 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (43, 1), (179089549, 1), (414515324343003503, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_43, prime_eightyOneCA_179089549, prime_eightyOneCA_414515324343003503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289631 : Nat.totient 95763617612328612068420289631 = 95217632890004746150531338240 := by
  rw [← show ((([(193, 1), (1913, 1), (603311179, 1), (429919250714021, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_193, prime_eightyOneCA_1913, prime_eightyOneCA_603311179, prime_eightyOneCA_429919250714021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289632 : Nat.totient 95763617612328612068420289632 = 46847767149173348867078763648 := by
  rw [← show ((([(2, 5), (47, 1), (3067, 1), (20760553665896184691799, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_47, prime_eightyOneCA_3067, prime_eightyOneCA_20760553665896184691799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289633 : Nat.totient 95763617612328612068420289633 = 63586958849954339731861644000 := by
  rw [← show ((([(3, 2), (251, 1), (57773, 1), (733769055943529042119, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_251, prime_eightyOneCA_57773, prime_eightyOneCA_733769055943529042119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289634 : Nat.totient 95763617612328612068420289634 = 47407731491251788152683311600 := by
  rw [← show ((([(2, 1), (101, 1), (474077314912517881526833117, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_101, prime_eightyOneCA_474077314912517881526833117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289635 : Nat.totient 95763617612328612068420289635 = 63319671757515482808667176960 := by
  rw [← show ((([(5, 1), (7, 1), (29, 1), (769, 1), (122689716172021257302261, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_7, prime_eightyOneCA_29, prime_eightyOneCA_769, prime_eightyOneCA_122689716172021257302261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289636 : Nat.totient 95763617612328612068420289636 = 31058470409366527649452497024 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (185307637, 1), (1163923014415161787, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_37, prime_eightyOneCA_185307637, prime_eightyOneCA_1163923014415161787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289637 : Nat.totient 95763617612328612068420289637 = 90129745454435171846109676800 := by
  rw [← show ((([(17, 1), (162901, 1), (546583, 1), (63266200321051367, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_17, prime_eightyOneCA_162901, prime_eightyOneCA_546583, prime_eightyOneCA_63266200321051367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289638 : Nat.totient 95763617612328612068420289638 = 45799329096311962764164210760 := by
  rw [← show ((([(2, 1), (23, 1), (69191, 1), (30087985058476634014483, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_23, prime_eightyOneCA_69191, prime_eightyOneCA_30087985058476634014483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289639 : Nat.totient 95763617612328612068420289639 = 62889534404546003091608787072 := by
  rw [← show ((([(3, 1), (67, 1), (12713749, 1), (109715213, 1), (341557638847, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_67, prime_eightyOneCA_12713749, prime_eightyOneCA_109715213, prime_eightyOneCA_341557638847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289640 : Nat.totient 95763617612328612068420289640 = 32939540931445586506285056000 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (19, 1), (709, 1), (8641, 1), (75013, 1), (3680657, 1), (6772081, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_11, prime_eightyOneCA_19, prime_eightyOneCA_709, prime_eightyOneCA_8641, prime_eightyOneCA_75013, prime_eightyOneCA_3680657, prime_eightyOneCA_6772081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289641 : Nat.totient 95763617612328612068420289641 = 87614909510473928878385965056 := by
  rw [← show ((([(13, 1), (113, 1), (1603055212393, 1), (40665888679573, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_13, prime_eightyOneCA_113, prime_eightyOneCA_1603055212393, prime_eightyOneCA_40665888679573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289642 : Nat.totient 95763617612328612068420289642 = 27361007224941847665725753472 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (1049677, 1), (87574387, 1), (8267938002733, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_7, prime_eightyOneCA_1049677, prime_eightyOneCA_87574387, prime_eightyOneCA_8267938002733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289643 : Nat.totient 95763617612328612068420289643 = 95524793309783338965962784000 := by
  rw [← show ((([(401, 1), (7773481, 1), (30721373602872632003, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_401, prime_eightyOneCA_7773481, prime_eightyOneCA_30721373602872632003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289644 : Nat.totient 95763617612328612068420289644 = 47881808806162832653577064000 := by
  rw [← show ((([(2, 2), (34073934234961, 1), (702616382305451, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_34073934234961, prime_eightyOneCA_702616382305451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289645 : Nat.totient 95763617612328612068420289645 = 50889546976659825619030563264 := by
  rw [← show ((([(3, 1), (5, 1), (277, 1), (23047802072762602182531959, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_277, prime_eightyOneCA_23047802072762602182531959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289646 : Nat.totient 95763617612328612068420289646 = 47877201247486941953602611840 := by
  rw [← show ((([(2, 1), (10399, 1), (27474289, 1), (35647831, 1), (4701315503, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_10399, prime_eightyOneCA_27474289, prime_eightyOneCA_35647831, prime_eightyOneCA_4701315503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289647 : Nat.totient 95763617612328612068420289647 = 92093455206975705612943363200 := by
  rw [← show ((([(31, 1), (167, 1), (3767, 1), (56773, 1), (86493787469467421, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_31, prime_eightyOneCA_167, prime_eightyOneCA_3767, prime_eightyOneCA_56773, prime_eightyOneCA_86493787469467421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289648 : Nat.totient 95763617612328612068420289648 = 31921050617278653957854212032 := by
  rw [← show ((([(2, 4), (3, 1), (205607, 1), (9703343596879059328843, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_205607, prime_eightyOneCA_9703343596879059328843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289649 : Nat.totient 95763617612328612068420289649 = 82025935071779597844268627200 := by
  rw [← show ((([(7, 1), (1873, 1), (6151, 1), (21654383, 1), (54836936613023, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_7, prime_eightyOneCA_1873, prime_eightyOneCA_6151, prime_eightyOneCA_21654383, prime_eightyOneCA_54836936613023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289650 : Nat.totient 95763617612328612068420289650 = 38305368036771774239491712960 := by
  rw [← show ((([(2, 1), (5, 2), (484829, 1), (3950407983529393335317, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_484829, prime_eightyOneCA_3950407983529393335317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289651 : Nat.totient 95763617612328612068420289651 = 57717901122448184069364280800 := by
  rw [← show ((([(3, 3), (11, 1), (181, 1), (1781416701310129137943343, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_11, prime_eightyOneCA_181, prime_eightyOneCA_1781416701310129137943343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289652 : Nat.totient 95763617612328612068420289652 = 47843400690647045820721382400 := by
  rw [← show ((([(2, 2), (1249, 1), (664669, 1), (3939805151, 1), (7319778623, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_1249, prime_eightyOneCA_664669, prime_eightyOneCA_3939805151, prime_eightyOneCA_7319778623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289653 : Nat.totient 95763617612328612068420289653 = 95763617612328612068420289652 := by
  rw [← show ((([(95763617612328612068420289653, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_95763617612328612068420289653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289654 : Nat.totient 95763617612328612068420289654 = 27532790373118494461385959424 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (17, 1), (139, 1), (188653, 1), (2754092380280141587, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_13, prime_eightyOneCA_17, prime_eightyOneCA_139, prime_eightyOneCA_188653, prime_eightyOneCA_2754092380280141587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289655 : Nat.totient 95763617612328612068420289655 = 75867004246822008404016518400 := by
  rw [← show ((([(5, 1), (103, 1), (1259051, 1), (2199209, 1), (67155794015903, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_103, prime_eightyOneCA_1259051, prime_eightyOneCA_2199209, prime_eightyOneCA_67155794015903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289656 : Nat.totient 95763617612328612068420289656 = 40618441637475298524295713792 := by
  rw [← show ((([(2, 3), (7, 1), (97, 1), (54632410447, 1), (322693650468439, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_7, prime_eightyOneCA_97, prime_eightyOneCA_54632410447, prime_eightyOneCA_322693650468439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289657 : Nat.totient 95763617612328612068420289657 = 61868400902113568502193459200 := by
  rw [← show ((([(3, 1), (73, 1), (79, 1), (233, 1), (1787, 1), (73387, 1), (739031, 1), (245113411, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_73, prime_eightyOneCA_79, prime_eightyOneCA_233, prime_eightyOneCA_1787, prime_eightyOneCA_73387, prime_eightyOneCA_739031, prime_eightyOneCA_245113411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289658 : Nat.totient 95763617612328612068420289658 = 47881781520734729948570232960 := by
  rw [← show ((([(2, 1), (1754849, 1), (27285429576085638157021, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_1754849, prime_eightyOneCA_27285429576085638157021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289659 : Nat.totient 95763617612328612068420289659 = 90723427211094237090749462832 := by
  rw [← show ((([(19, 2), (154964198047, 1), (1711835264691677, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_19, prime_eightyOneCA_154964198047, prime_eightyOneCA_1711835264691677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289660 : Nat.totient 95763617612328612068420289660 = 25536964694284044370910211840 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (10927623977, 1), (48685798391859331, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_10927623977, prime_eightyOneCA_48685798391859331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289661 : Nat.totient 95763617612328612068420289661 = 91541970675705595081291888512 := by
  rw [← show ((([(23, 1), (1579, 1), (2636881284586519042553633, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_23, prime_eightyOneCA_1579, prime_eightyOneCA_2636881284586519042553633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289662 : Nat.totient 95763617612328612068420289662 = 42291023593414113213459840000 := by
  rw [← show ((([(2, 1), (11, 1), (41, 1), (241, 1), (440531495764730345973541, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_11, prime_eightyOneCA_41, prime_eightyOneCA_241, prime_eightyOneCA_440531495764730345973541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289663 : Nat.totient 95763617612328612068420289663 = 53794574542504378167230884320 := by
  rw [← show ((([(3, 1), (7, 1), (59, 1), (4920174722171, 1), (15709006232827, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_7, prime_eightyOneCA_59, prime_eightyOneCA_4920174722171, prime_eightyOneCA_15709006232827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289664 : Nat.totient 95763617612328612068420289664 = 46228428380415499341759713280 := by
  rw [← show ((([(2, 7), (29, 1), (20663, 1), (1000541, 1), (1247855538106759, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_29, prime_eightyOneCA_20663, prime_eightyOneCA_1000541, prime_eightyOneCA_1247855538106759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289665 : Nat.totient 95763617612328612068420289665 = 76351176313311062310701400000 := by
  rw [← show ((([(5, 1), (367, 1), (1499, 1), (20334088351, 1), (1712135515751, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_367, prime_eightyOneCA_1499, prime_eightyOneCA_20334088351, prime_eightyOneCA_1712135515751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289666 : Nat.totient 95763617612328612068420289666 = 31921205870776204022806763220 := by
  rw [← show ((([(2, 1), (3, 1), (15960602935388102011403381611, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_15960602935388102011403381611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289667 : Nat.totient 95763617612328612068420289667 = 86729314063995724137437242848 := by
  rw [← show ((([(13, 1), (53, 1), (138989285358967506630508403, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_13, prime_eightyOneCA_53, prime_eightyOneCA_138989285358967506630508403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289668 : Nat.totient 95763617612328612068420289668 = 47881808806161882446389939752 := by
  rw [← show ((([(2, 2), (20089635416803, 1), (1191704274685739, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_20089635416803, prime_eightyOneCA_1191704274685739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289669 : Nat.totient 95763617612328612068420289669 = 63817894109182671231230340000 := by
  rw [← show ((([(3, 2), (2621, 1), (399871, 1), (10152455735961304351, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_2621, prime_eightyOneCA_399871, prime_eightyOneCA_10152455735961304351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289670 : Nat.totient 95763617612328612068420289670 = 32833240324226952709172670576 := by
  rw [← show ((([(2, 1), (5, 1), (7, 2), (195435954310874718506980183, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_7, prime_eightyOneCA_195435954310874718506980183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289671 : Nat.totient 95763617612328612068420289671 = 90130455977942788105427339008 := by
  rw [← show ((([(17, 1), (11770697, 1), (478574376453306096479, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_17, prime_eightyOneCA_11770697, prime_eightyOneCA_478574376453306096479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289672 : Nat.totient 95763617612328612068420289672 = 31901586199067060689049647104 := by
  rw [← show ((([(2, 3), (3, 1), (1627, 1), (2452458963642916719637889, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_1627, prime_eightyOneCA_2452458963642916719637889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289673 : Nat.totient 95763617612328612068420289673 = 82179769189858172991158837760 := by
  rw [← show ((([(11, 1), (37, 1), (43, 1), (149, 1), (36724121080838951894377, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_11, prime_eightyOneCA_37, prime_eightyOneCA_43, prime_eightyOneCA_149, prime_eightyOneCA_36724121080838951894377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289674 : Nat.totient 95763617612328612068420289674 = 47096861120817350197583748960 := by
  rw [← show ((([(2, 1), (61, 1), (784947685346955836626395817, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_61, prime_eightyOneCA_784947685346955836626395817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289675 : Nat.totient 95763617612328612068420289675 = 51073929393241926436490821120 := by
  rw [← show ((([(3, 1), (5, 2), (1276848234831048160912270529, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_1276848234831048160912270529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289676 : Nat.totient 95763617612328612068420289676 = 47436274912788063249436353600 := by
  rw [← show ((([(2, 2), (109, 1), (10651, 1), (26399, 1), (781153159830006659, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_109, prime_eightyOneCA_10651, prime_eightyOneCA_26399, prime_eightyOneCA_781153159830006659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289677 : Nat.totient 95763617612328612068420289677 = 82082051194813375310496608832 := by
  rw [← show ((([(7, 1), (78203, 1), (174935959001077072433137, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_7, prime_eightyOneCA_78203, prime_eightyOneCA_174935959001077072433137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289678 : Nat.totient 95763617612328612068420289678 = 29250830727168531215416335360 := by
  rw [← show ((([(2, 1), (3, 3), (19, 1), (31, 1), (1979, 1), (10198049, 1), (149186182379803, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_19, prime_eightyOneCA_31, prime_eightyOneCA_1979, prime_eightyOneCA_10198049, prime_eightyOneCA_149186182379803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289679 : Nat.totient 95763617612328612068420289679 = 93686563612664309362505551200 := by
  rw [← show ((([(47, 1), (2371, 1), (3739915111, 1), (229778498537597, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_47, prime_eightyOneCA_2371, prime_eightyOneCA_3739915111, prime_eightyOneCA_229778498537597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289680 : Nat.totient 95763617612328612068420289680 = 35358862216478014789513543680 := by
  rw [← show ((([(2, 4), (5, 1), (13, 1), (2951777, 1), (31194904476292068521, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_13, prime_eightyOneCA_2951777, prime_eightyOneCA_31194904476292068521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289681 : Nat.totient 95763617612328612068420289681 = 63525927290709938534973791744 := by
  rw [← show ((([(3, 1), (263, 1), (863, 1), (1526387, 1), (92139974206861409, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_263, prime_eightyOneCA_863, prime_eightyOneCA_1526387, prime_eightyOneCA_92139974206861409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289682 : Nat.totient 95763617612328612068420289682 = 47667092130064688262853534992 := by
  rw [← show ((([(2, 1), (223, 1), (1066811299, 1), (201269551249641533, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_223, prime_eightyOneCA_1066811299, prime_eightyOneCA_201269551249641533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289683 : Nat.totient 95763617612328612068420289683 = 95763596221659753026970430048 := by
  rw [← show ((([(4842653, 1), (59272979, 1), (333626422112309, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_4842653, prime_eightyOneCA_59272979, prime_eightyOneCA_333626422112309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289684 : Nat.totient 95763617612328612068420289684 = 23720323365722874018184214400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11, 1), (23, 1), (331, 1), (13613592381613219707407, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_7, prime_eightyOneCA_11, prime_eightyOneCA_23, prime_eightyOneCA_331, prime_eightyOneCA_13613592381613219707407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289685 : Nat.totient 95763617612328612068420289685 = 76610691520084515431473254720 := by
  rw [← show ((([(5, 1), (418079, 1), (3964381, 1), (11555714404150363, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_418079, prime_eightyOneCA_3964381, prime_eightyOneCA_11555714404150363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289686 : Nat.totient 95763617612328612068420289686 = 47822622392312434209693197008 := by
  rw [← show ((([(2, 1), (809, 1), (59186413851871824516947027, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_809, prime_eightyOneCA_59186413851871824516947027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289687 : Nat.totient 95763617612328612068420289687 = 63841636844554335703791050880 := by
  rw [← show ((([(3, 2), (98327, 1), (540713, 1), (8469283, 1), (23630438971, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_98327, prime_eightyOneCA_540713, prime_eightyOneCA_8469283, prime_eightyOneCA_23630438971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289688 : Nat.totient 95763617612328612068420289688 = 45052027823479805501793963520 := by
  rw [← show ((([(2, 3), (17, 1), (3413, 1), (206312407603127772850391, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_17, prime_eightyOneCA_3413, prime_eightyOneCA_206312407603127772850391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289689 : Nat.totient 95763617612328612068420289689 = 95357179269515430485552880000 := by
  rw [← show ((([(281, 1), (1511, 1), (38351, 1), (24120007, 1), (243823542847, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_281, prime_eightyOneCA_1511, prime_eightyOneCA_38351, prime_eightyOneCA_24120007, prime_eightyOneCA_243823542847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289690 : Nat.totient 95763617612328612068420289690 = 25536413249500606031451582144 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (46309, 1), (68930890044648349182247, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_5, prime_eightyOneCA_46309, prime_eightyOneCA_68930890044648349182247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289691 : Nat.totient 95763617612328612068420289691 = 82083100808252876461245009960 := by
  rw [← show ((([(7, 1), (35464644623, 1), (385750849816466531, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_7, prime_eightyOneCA_35464644623, prime_eightyOneCA_385750849816466531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289692 : Nat.totient 95763617612328612068420289692 = 47804203974956810244822870912 := by
  rw [← show ((([(2, 2), (617, 1), (140818963, 1), (210603919, 1), (1308361627, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_617, prime_eightyOneCA_140818963, prime_eightyOneCA_210603919, prime_eightyOneCA_1308361627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289693 : Nat.totient 95763617612328612068420289693 = 56899337785574559955772266944 := by
  rw [← show ((([(3, 1), (13, 1), (29, 1), (84671633609485952315137303, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_13, prime_eightyOneCA_29, prime_eightyOneCA_84671633609485952315137303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289694 : Nat.totient 95763617612328612068420289694 = 47532306552104712559507880880 := by
  rw [← show ((([(2, 1), (137, 1), (349502254059593474702263831, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_137, prime_eightyOneCA_349502254059593474702263831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289695 : Nat.totient 95763617612328612068420289695 = 69371318355227929294614835200 := by
  rw [← show ((([(5, 1), (11, 2), (431, 1), (613, 1), (14168489, 1), (42284761673977, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_5, prime_eightyOneCA_11, prime_eightyOneCA_431, prime_eightyOneCA_613, prime_eightyOneCA_14168489, prime_eightyOneCA_42284761673977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289696 : Nat.totient 95763617612328612068420289696 = 31921205870772700240772422656 := by
  rw [← show ((([(2, 5), (3, 2), (17535770129749, 1), (18961959394633, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_3, prime_eightyOneCA_17535770129749, prime_eightyOneCA_18961959394633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289697 : Nat.totient 95763617612328612068420289697 = 90714879695123048729311833600 := by
  rw [← show ((([(19, 1), (10691, 1), (1946059, 1), (6073211, 1), (39889100257, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_19, prime_eightyOneCA_10691, prime_eightyOneCA_1946059, prime_eightyOneCA_6073211, prime_eightyOneCA_39889100257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289698 : Nat.totient 95763617612328612068420289698 = 40457723980908706675983360000 := by
  rw [← show ((([(2, 1), (7, 1), (71, 1), (12899, 1), (29201, 1), (33961, 1), (687359, 1), (10957117, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_7, prime_eightyOneCA_71, prime_eightyOneCA_12899, prime_eightyOneCA_29201, prime_eightyOneCA_33961, prime_eightyOneCA_687359, prime_eightyOneCA_10957117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289699 : Nat.totient 95763617612328612068420289699 = 63842411741552408045613526464 := by
  rw [← show ((([(3, 1), (31921205870776204022806763233, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_3, prime_eightyOneCA_31921205870776204022806763233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289700 : Nat.totient 95763617612328612068420289700 = 38284992963752426332968683520 := by
  rw [← show ((([(2, 2), (5, 2), (1907, 1), (134087, 1), (468049, 1), (8001508204717, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_2, prime_eightyOneCA_5, prime_eightyOneCA_1907, prime_eightyOneCA_134087, prime_eightyOneCA_468049, prime_eightyOneCA_8001508204717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyOneCA_95763617612328612068420289701 : Nat.totient 95763617612328612068420289701 = 95425230270942291884432938572 := by
  rw [← show ((([(283, 1), (338387341386320183987350847, 1)] : List FactorBlock).map factorBlockValue).prod) = 95763617612328612068420289701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyOneCA_283, prime_eightyOneCA_338387341386320183987350847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyOneCA : certifiedKill 1 95763617612328612068420289599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyOneCA_95763617612328612068420289600, phi_eightyOneCA_95763617612328612068420289601, phi_eightyOneCA_95763617612328612068420289602,
    phi_eightyOneCA_95763617612328612068420289603, phi_eightyOneCA_95763617612328612068420289604, phi_eightyOneCA_95763617612328612068420289605,
    phi_eightyOneCA_95763617612328612068420289606, phi_eightyOneCA_95763617612328612068420289607, phi_eightyOneCA_95763617612328612068420289608,
    phi_eightyOneCA_95763617612328612068420289609, phi_eightyOneCA_95763617612328612068420289610, phi_eightyOneCA_95763617612328612068420289611,
    phi_eightyOneCA_95763617612328612068420289612, phi_eightyOneCA_95763617612328612068420289613, phi_eightyOneCA_95763617612328612068420289614,
    phi_eightyOneCA_95763617612328612068420289615, phi_eightyOneCA_95763617612328612068420289616, phi_eightyOneCA_95763617612328612068420289617,
    phi_eightyOneCA_95763617612328612068420289618, phi_eightyOneCA_95763617612328612068420289619, phi_eightyOneCA_95763617612328612068420289620,
    phi_eightyOneCA_95763617612328612068420289621, phi_eightyOneCA_95763617612328612068420289622, phi_eightyOneCA_95763617612328612068420289623,
    phi_eightyOneCA_95763617612328612068420289624, phi_eightyOneCA_95763617612328612068420289625, phi_eightyOneCA_95763617612328612068420289626,
    phi_eightyOneCA_95763617612328612068420289627, phi_eightyOneCA_95763617612328612068420289628, phi_eightyOneCA_95763617612328612068420289629,
    phi_eightyOneCA_95763617612328612068420289630, phi_eightyOneCA_95763617612328612068420289631, phi_eightyOneCA_95763617612328612068420289632,
    phi_eightyOneCA_95763617612328612068420289633, phi_eightyOneCA_95763617612328612068420289634, phi_eightyOneCA_95763617612328612068420289635,
    phi_eightyOneCA_95763617612328612068420289636, phi_eightyOneCA_95763617612328612068420289637, phi_eightyOneCA_95763617612328612068420289638,
    phi_eightyOneCA_95763617612328612068420289639, phi_eightyOneCA_95763617612328612068420289640, phi_eightyOneCA_95763617612328612068420289641,
    phi_eightyOneCA_95763617612328612068420289642, phi_eightyOneCA_95763617612328612068420289643, phi_eightyOneCA_95763617612328612068420289644,
    phi_eightyOneCA_95763617612328612068420289645, phi_eightyOneCA_95763617612328612068420289646, phi_eightyOneCA_95763617612328612068420289647,
    phi_eightyOneCA_95763617612328612068420289648, phi_eightyOneCA_95763617612328612068420289649, phi_eightyOneCA_95763617612328612068420289650,
    phi_eightyOneCA_95763617612328612068420289651, phi_eightyOneCA_95763617612328612068420289652, phi_eightyOneCA_95763617612328612068420289653,
    phi_eightyOneCA_95763617612328612068420289654, phi_eightyOneCA_95763617612328612068420289655, phi_eightyOneCA_95763617612328612068420289656,
    phi_eightyOneCA_95763617612328612068420289657, phi_eightyOneCA_95763617612328612068420289658, phi_eightyOneCA_95763617612328612068420289659,
    phi_eightyOneCA_95763617612328612068420289660, phi_eightyOneCA_95763617612328612068420289661, phi_eightyOneCA_95763617612328612068420289662,
    phi_eightyOneCA_95763617612328612068420289663, phi_eightyOneCA_95763617612328612068420289664, phi_eightyOneCA_95763617612328612068420289665,
    phi_eightyOneCA_95763617612328612068420289666, phi_eightyOneCA_95763617612328612068420289667, phi_eightyOneCA_95763617612328612068420289668,
    phi_eightyOneCA_95763617612328612068420289669, phi_eightyOneCA_95763617612328612068420289670, phi_eightyOneCA_95763617612328612068420289671,
    phi_eightyOneCA_95763617612328612068420289672, phi_eightyOneCA_95763617612328612068420289673, phi_eightyOneCA_95763617612328612068420289674,
    phi_eightyOneCA_95763617612328612068420289675, phi_eightyOneCA_95763617612328612068420289676, phi_eightyOneCA_95763617612328612068420289677,
    phi_eightyOneCA_95763617612328612068420289678, phi_eightyOneCA_95763617612328612068420289679, phi_eightyOneCA_95763617612328612068420289680,
    phi_eightyOneCA_95763617612328612068420289681, phi_eightyOneCA_95763617612328612068420289682, phi_eightyOneCA_95763617612328612068420289683,
    phi_eightyOneCA_95763617612328612068420289684, phi_eightyOneCA_95763617612328612068420289685, phi_eightyOneCA_95763617612328612068420289686,
    phi_eightyOneCA_95763617612328612068420289687, phi_eightyOneCA_95763617612328612068420289688, phi_eightyOneCA_95763617612328612068420289689,
    phi_eightyOneCA_95763617612328612068420289690, phi_eightyOneCA_95763617612328612068420289691, phi_eightyOneCA_95763617612328612068420289692,
    phi_eightyOneCA_95763617612328612068420289693, phi_eightyOneCA_95763617612328612068420289694, phi_eightyOneCA_95763617612328612068420289695,
    phi_eightyOneCA_95763617612328612068420289696, phi_eightyOneCA_95763617612328612068420289697, phi_eightyOneCA_95763617612328612068420289698,
    phi_eightyOneCA_95763617612328612068420289699, phi_eightyOneCA_95763617612328612068420289700, phi_eightyOneCA_95763617612328612068420289701]

end TotientTailPeriodKiller
end Erdos249257
