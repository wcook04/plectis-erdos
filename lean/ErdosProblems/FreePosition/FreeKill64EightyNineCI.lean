import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyNineCIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyNineCIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyNineCIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyNineCIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyNineCIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyNineCIFastPow a n * eightyNineCIFastPow a n * a else eightyNineCIFastPow a n * eightyNineCIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyNineCI_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyNineCI_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyNineCI_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyNineCI_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyNineCI_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyNineCI_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyNineCI_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyNineCI_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyNineCI_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyNineCI_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyNineCI_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyNineCI_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyNineCI_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyNineCI_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyNineCI_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyNineCI_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyNineCI_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyNineCI_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyNineCI_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyNineCI_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyNineCI_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyNineCI_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyNineCI_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyNineCI_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyNineCI_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyNineCI_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyNineCI_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyNineCI_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyNineCI_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyNineCI_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyNineCI_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyNineCI_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyNineCI_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyNineCI_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyNineCI_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyNineCI_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyNineCI_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightyNineCI_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyNineCI_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyNineCI_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyNineCI_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightyNineCI_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyNineCI_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyNineCI_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightyNineCI_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyNineCI_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightyNineCI_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyNineCI_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightyNineCI_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightyNineCI_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightyNineCI_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightyNineCI_257 : Nat.Prime 257 := by norm_num

private theorem prime_eightyNineCI_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyNineCI_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyNineCI_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightyNineCI_293 : Nat.Prime 293 := by norm_num

private theorem prime_eightyNineCI_307 : Nat.Prime 307 := by norm_num

private theorem prime_eightyNineCI_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightyNineCI_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyNineCI_337 : Nat.Prime 337 := by norm_num

private theorem prime_eightyNineCI_359 : Nat.Prime 359 := by norm_num

private theorem prime_eightyNineCI_367 : Nat.Prime 367 := by norm_num

private theorem prime_eightyNineCI_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyNineCI_401 : Nat.Prime 401 := by norm_num

private theorem prime_eightyNineCI_409 : Nat.Prime 409 := by norm_num

private theorem prime_eightyNineCI_419 : Nat.Prime 419 := by norm_num

private theorem prime_eightyNineCI_433 : Nat.Prime 433 := by norm_num

private theorem prime_eightyNineCI_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightyNineCI_463 : Nat.Prime 463 := by norm_num

private theorem prime_eightyNineCI_479 : Nat.Prime 479 := by norm_num

private theorem prime_eightyNineCI_487 : Nat.Prime 487 := by norm_num

private theorem prime_eightyNineCI_491 : Nat.Prime 491 := by norm_num

private theorem prime_eightyNineCI_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightyNineCI_509 : Nat.Prime 509 := by norm_num

private theorem prime_eightyNineCI_521 : Nat.Prime 521 := by norm_num

private theorem prime_eightyNineCI_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyNineCI_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightyNineCI_557 : Nat.Prime 557 := by norm_num

private theorem prime_eightyNineCI_569 : Nat.Prime 569 := by norm_num

private theorem prime_eightyNineCI_577 : Nat.Prime 577 := by norm_num

private theorem prime_eightyNineCI_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightyNineCI_647 : Nat.Prime 647 := by norm_num

private theorem prime_eightyNineCI_677 : Nat.Prime 677 := by norm_num

private theorem prime_eightyNineCI_683 : Nat.Prime 683 := by norm_num

private theorem prime_eightyNineCI_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightyNineCI_719 : Nat.Prime 719 := by norm_num

private theorem prime_eightyNineCI_739 : Nat.Prime 739 := by norm_num

private theorem prime_eightyNineCI_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightyNineCI_773 : Nat.Prime 773 := by norm_num

private theorem prime_eightyNineCI_809 : Nat.Prime 809 := by norm_num

private theorem prime_eightyNineCI_811 : Nat.Prime 811 := by norm_num

private theorem prime_eightyNineCI_821 : Nat.Prime 821 := by norm_num

private theorem prime_eightyNineCI_823 : Nat.Prime 823 := by norm_num

private theorem prime_eightyNineCI_853 : Nat.Prime 853 := by norm_num

private theorem prime_eightyNineCI_857 : Nat.Prime 857 := by norm_num

private theorem prime_eightyNineCI_877 : Nat.Prime 877 := by norm_num

private theorem prime_eightyNineCI_907 : Nat.Prime 907 := by norm_num

private theorem prime_eightyNineCI_911 : Nat.Prime 911 := by norm_num

private theorem prime_eightyNineCI_937 : Nat.Prime 937 := by norm_num

private theorem prime_eightyNineCI_941 : Nat.Prime 941 := by norm_num

private theorem prime_eightyNineCI_953 : Nat.Prime 953 := by norm_num

private theorem prime_eightyNineCI_967 : Nat.Prime 967 := by norm_num

private theorem prime_eightyNineCI_971 : Nat.Prime 971 := by norm_num

private theorem prime_eightyNineCI_983 : Nat.Prime 983 := by norm_num

private theorem prime_eightyNineCI_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_eightyNineCI_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightyNineCI_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_eightyNineCI_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_eightyNineCI_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_eightyNineCI_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_eightyNineCI_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_eightyNineCI_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_eightyNineCI_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_eightyNineCI_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_eightyNineCI_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_eightyNineCI_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_eightyNineCI_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_eightyNineCI_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_eightyNineCI_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_eightyNineCI_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_eightyNineCI_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_eightyNineCI_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_eightyNineCI_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_eightyNineCI_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_eightyNineCI_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_eightyNineCI_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_eightyNineCI_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_eightyNineCI_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_eightyNineCI_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_eightyNineCI_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_eightyNineCI_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_eightyNineCI_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_eightyNineCI_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_eightyNineCI_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_eightyNineCI_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_eightyNineCI_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_eightyNineCI_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_eightyNineCI_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_eightyNineCI_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_eightyNineCI_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_eightyNineCI_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_eightyNineCI_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_eightyNineCI_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_eightyNineCI_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_eightyNineCI_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_eightyNineCI_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_eightyNineCI_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_eightyNineCI_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_eightyNineCI_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_eightyNineCI_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_eightyNineCI_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_eightyNineCI_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_eightyNineCI_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_eightyNineCI_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_eightyNineCI_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_eightyNineCI_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_eightyNineCI_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_eightyNineCI_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_eightyNineCI_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_eightyNineCI_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_eightyNineCI_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_eightyNineCI_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_eightyNineCI_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_eightyNineCI_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_eightyNineCI_4409 : Nat.Prime 4409 := by norm_num

private theorem prime_eightyNineCI_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_eightyNineCI_4483 : Nat.Prime 4483 := by norm_num

private theorem prime_eightyNineCI_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_eightyNineCI_4799 : Nat.Prime 4799 := by norm_num

private theorem prime_eightyNineCI_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_eightyNineCI_5153 : Nat.Prime 5153 := by norm_num

private theorem prime_eightyNineCI_5167 : Nat.Prime 5167 := by norm_num

private theorem prime_eightyNineCI_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_eightyNineCI_5903 : Nat.Prime 5903 := by norm_num

private theorem prime_eightyNineCI_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_eightyNineCI_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_eightyNineCI_6481 : Nat.Prime 6481 := by norm_num

private theorem prime_eightyNineCI_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_eightyNineCI_6703 : Nat.Prime 6703 := by norm_num

private theorem prime_eightyNineCI_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_eightyNineCI_7057 : Nat.Prime 7057 := by norm_num

private theorem prime_eightyNineCI_7583 : Nat.Prime 7583 := by norm_num

private theorem prime_eightyNineCI_7603 : Nat.Prime 7603 := by norm_num

private theorem prime_eightyNineCI_7883 : Nat.Prime 7883 := by norm_num

private theorem prime_eightyNineCI_7901 : Nat.Prime 7901 := by norm_num

private theorem prime_eightyNineCI_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_eightyNineCI_8233 : Nat.Prime 8233 := by norm_num

private theorem prime_eightyNineCI_8353 : Nat.Prime 8353 := by norm_num

private theorem prime_eightyNineCI_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_eightyNineCI_9619 : Nat.Prime 9619 := by norm_num

private theorem prime_eightyNineCI_9643 : Nat.Prime 9643 := by norm_num

private theorem prime_eightyNineCI_9649 : Nat.Prime 9649 := by norm_num

private theorem prime_eightyNineCI_9677 : Nat.Prime 9677 := by norm_num

private theorem prime_eightyNineCI_10177 : Nat.Prime 10177 := by norm_num

private theorem prime_eightyNineCI_10739 : Nat.Prime 10739 := by norm_num

private theorem prime_eightyNineCI_11261 : Nat.Prime 11261 := by norm_num

private theorem prime_eightyNineCI_11353 : Nat.Prime 11353 := by norm_num

private theorem prime_eightyNineCI_11731 : Nat.Prime 11731 := by norm_num

private theorem prime_eightyNineCI_11827 : Nat.Prime 11827 := by norm_num

private theorem prime_eightyNineCI_12113 : Nat.Prime 12113 := by norm_num

private theorem prime_eightyNineCI_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_eightyNineCI_13241 : Nat.Prime 13241 := by norm_num

private theorem prime_eightyNineCI_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_eightyNineCI_14489 : Nat.Prime 14489 := by norm_num

private theorem prime_eightyNineCI_15791 : Nat.Prime 15791 := by norm_num

private theorem prime_eightyNineCI_16927 : Nat.Prime 16927 := by norm_num

private theorem prime_eightyNineCI_17077 : Nat.Prime 17077 := by norm_num

private theorem prime_eightyNineCI_17971 : Nat.Prime 17971 := by norm_num

private theorem prime_eightyNineCI_19391 : Nat.Prime 19391 := by norm_num

private theorem prime_eightyNineCI_19447 : Nat.Prime 19447 := by norm_num

private theorem prime_eightyNineCI_20231 : Nat.Prime 20231 := by norm_num

private theorem prime_eightyNineCI_20297 : Nat.Prime 20297 := by norm_num

private theorem prime_eightyNineCI_20947 : Nat.Prime 20947 := by norm_num

private theorem prime_eightyNineCI_21107 : Nat.Prime 21107 := by norm_num

private theorem prime_eightyNineCI_21871 : Nat.Prime 21871 := by norm_num

private theorem prime_eightyNineCI_21943 : Nat.Prime 21943 := by norm_num

private theorem prime_eightyNineCI_24083 : Nat.Prime 24083 := by norm_num

private theorem prime_eightyNineCI_24137 : Nat.Prime 24137 := by norm_num

private theorem prime_eightyNineCI_24197 : Nat.Prime 24197 := by norm_num

private theorem prime_eightyNineCI_25951 : Nat.Prime 25951 := by norm_num

private theorem prime_eightyNineCI_26293 : Nat.Prime 26293 := by norm_num

private theorem prime_eightyNineCI_26891 : Nat.Prime 26891 := by norm_num

private theorem prime_eightyNineCI_27803 : Nat.Prime 27803 := by norm_num

private theorem prime_eightyNineCI_28319 : Nat.Prime 28319 := by norm_num

private theorem prime_eightyNineCI_31799 : Nat.Prime 31799 := by norm_num

private theorem prime_eightyNineCI_35069 : Nat.Prime 35069 := by norm_num

private theorem prime_eightyNineCI_35569 : Nat.Prime 35569 := by norm_num

private theorem prime_eightyNineCI_36217 : Nat.Prime 36217 := by norm_num

private theorem prime_eightyNineCI_36691 : Nat.Prime 36691 := by norm_num

private theorem prime_eightyNineCI_38299 : Nat.Prime 38299 := by norm_num

private theorem prime_eightyNineCI_39607 : Nat.Prime 39607 := by norm_num

private theorem prime_eightyNineCI_39877 : Nat.Prime 39877 := by norm_num

private theorem prime_eightyNineCI_42187 : Nat.Prime 42187 := by norm_num

private theorem prime_eightyNineCI_42937 : Nat.Prime 42937 := by norm_num

private theorem prime_eightyNineCI_43997 : Nat.Prime 43997 := by norm_num

private theorem prime_eightyNineCI_45127 : Nat.Prime 45127 := by norm_num

private theorem prime_eightyNineCI_47777 : Nat.Prime 47777 := by norm_num

private theorem prime_eightyNineCI_50069 : Nat.Prime 50069 := by norm_num

private theorem prime_eightyNineCI_54421 : Nat.Prime 54421 := by norm_num

private theorem prime_eightyNineCI_58099 : Nat.Prime 58099 := by norm_num

private theorem prime_eightyNineCI_59233 : Nat.Prime 59233 := by norm_num

private theorem prime_eightyNineCI_61339 : Nat.Prime 61339 := by norm_num

private theorem prime_eightyNineCI_65719 : Nat.Prime 65719 := by norm_num

private theorem prime_eightyNineCI_66083 : Nat.Prime 66083 := by norm_num

private theorem prime_eightyNineCI_70429 : Nat.Prime 70429 := by norm_num

private theorem prime_eightyNineCI_71483 : Nat.Prime 71483 := by norm_num

private theorem prime_eightyNineCI_72269 : Nat.Prime 72269 := by norm_num

private theorem prime_eightyNineCI_72707 : Nat.Prime 72707 := by norm_num

private theorem prime_eightyNineCI_76079 : Nat.Prime 76079 := by norm_num

private theorem prime_eightyNineCI_80347 : Nat.Prime 80347 := by norm_num

private theorem prime_eightyNineCI_81049 : Nat.Prime 81049 := by norm_num

private theorem prime_eightyNineCI_81839 : Nat.Prime 81839 := by norm_num

private theorem prime_eightyNineCI_82799 : Nat.Prime 82799 := by norm_num

private theorem prime_eightyNineCI_84731 : Nat.Prime 84731 := by norm_num

private theorem prime_eightyNineCI_85597 : Nat.Prime 85597 := by norm_num

private theorem prime_eightyNineCI_91127 : Nat.Prime 91127 := by norm_num

private theorem prime_eightyNineCI_92143 : Nat.Prime 92143 := by norm_num

private theorem prime_eightyNineCI_92641 : Nat.Prime 92641 := by norm_num

private theorem prime_eightyNineCI_97861 : Nat.Prime 97861 := by norm_num

private theorem prime_eightyNineCI_99929 : Nat.Prime 99929 := by norm_num

private theorem prime_eightyNineCI_106357 : Nat.Prime 106357 := by norm_num

private theorem prime_eightyNineCI_109201 : Nat.Prime 109201 := by norm_num

private theorem prime_eightyNineCI_110533 : Nat.Prime 110533 := by norm_num

private theorem prime_eightyNineCI_112361 : Nat.Prime 112361 := by norm_num

private theorem prime_eightyNineCI_112913 : Nat.Prime 112913 := by norm_num

private theorem prime_eightyNineCI_115303 : Nat.Prime 115303 := by norm_num

private theorem prime_eightyNineCI_130657 : Nat.Prime 130657 := by norm_num

private theorem prime_eightyNineCI_131899 : Nat.Prime 131899 := by norm_num

private theorem prime_eightyNineCI_133073 : Nat.Prime 133073 := by norm_num

private theorem prime_eightyNineCI_135781 : Nat.Prime 135781 := by norm_num

private theorem prime_eightyNineCI_136651 : Nat.Prime 136651 := by norm_num

private theorem prime_eightyNineCI_138893 : Nat.Prime 138893 := by norm_num

private theorem prime_eightyNineCI_139661 : Nat.Prime 139661 := by norm_num

private theorem prime_eightyNineCI_145549 : Nat.Prime 145549 := by norm_num

private theorem prime_eightyNineCI_153437 : Nat.Prime 153437 := by norm_num

private theorem prime_eightyNineCI_158269 : Nat.Prime 158269 := by norm_num

private theorem prime_eightyNineCI_163063 : Nat.Prime 163063 := by norm_num

private theorem prime_eightyNineCI_167077 : Nat.Prime 167077 := by norm_num

private theorem prime_eightyNineCI_172541 : Nat.Prime 172541 := by norm_num

private theorem prime_eightyNineCI_175327 : Nat.Prime 175327 := by norm_num

private theorem prime_eightyNineCI_179827 : Nat.Prime 179827 := by norm_num

private theorem prime_eightyNineCI_185683 : Nat.Prime 185683 := by norm_num

private theorem prime_eightyNineCI_191627 : Nat.Prime 191627 := by norm_num

private theorem prime_eightyNineCI_193327 : Nat.Prime 193327 := by norm_num

private theorem prime_eightyNineCI_197369 : Nat.Prime 197369 := by norm_num

private theorem prime_eightyNineCI_204443 : Nat.Prime 204443 := by norm_num

private theorem prime_eightyNineCI_204623 : Nat.Prime 204623 := by norm_num

private theorem prime_eightyNineCI_206047 : Nat.Prime 206047 := by norm_num

private theorem prime_eightyNineCI_215389 : Nat.Prime 215389 := by norm_num

private theorem prime_eightyNineCI_233747 : Nat.Prime 233747 := by norm_num

private theorem prime_eightyNineCI_245083 : Nat.Prime 245083 := by norm_num

private theorem prime_eightyNineCI_258067 : Nat.Prime 258067 := by norm_num

private theorem prime_eightyNineCI_261167 : Nat.Prime 261167 := by norm_num

private theorem prime_eightyNineCI_264211 : Nat.Prime 264211 := by norm_num

private theorem prime_eightyNineCI_266239 : Nat.Prime 266239 := by norm_num

private theorem prime_eightyNineCI_278687 : Nat.Prime 278687 := by norm_num

private theorem prime_eightyNineCI_280913 : Nat.Prime 280913 := by norm_num

private theorem prime_eightyNineCI_285119 : Nat.Prime 285119 := by norm_num

private theorem prime_eightyNineCI_288877 : Nat.Prime 288877 := by norm_num

private theorem prime_eightyNineCI_305971 : Nat.Prime 305971 := by norm_num

private theorem prime_eightyNineCI_316663 : Nat.Prime 316663 := by norm_num

private theorem prime_eightyNineCI_324839 : Nat.Prime 324839 := by norm_num

private theorem prime_eightyNineCI_330721 : Nat.Prime 330721 := by norm_num

private theorem prime_eightyNineCI_333349 : Nat.Prime 333349 := by norm_num

private theorem prime_eightyNineCI_334043 : Nat.Prime 334043 := by norm_num

private theorem prime_eightyNineCI_375043 : Nat.Prime 375043 := by norm_num

private theorem prime_eightyNineCI_417007 : Nat.Prime 417007 := by norm_num

private theorem prime_eightyNineCI_436621 : Nat.Prime 436621 := by norm_num

private theorem prime_eightyNineCI_439961 : Nat.Prime 439961 := by norm_num

private theorem prime_eightyNineCI_450727 : Nat.Prime 450727 := by norm_num

private theorem prime_eightyNineCI_453199 : Nat.Prime 453199 := by norm_num

private theorem prime_eightyNineCI_483389 : Nat.Prime 483389 := by norm_num

private theorem prime_eightyNineCI_513257 : Nat.Prime 513257 := by norm_num

private theorem prime_eightyNineCI_525893 : Nat.Prime 525893 := by norm_num

private theorem prime_eightyNineCI_562669 : Nat.Prime 562669 := by norm_num

private theorem prime_eightyNineCI_604529 : Nat.Prime 604529 := by norm_num

private theorem prime_eightyNineCI_640019 : Nat.Prime 640019 := by norm_num

private theorem prime_eightyNineCI_649483 : Nat.Prime 649483 := by norm_num

private theorem prime_eightyNineCI_663359 : Nat.Prime 663359 := by norm_num

private theorem prime_eightyNineCI_663763 : Nat.Prime 663763 := by norm_num

private theorem prime_eightyNineCI_690467 : Nat.Prime 690467 := by norm_num

private theorem prime_eightyNineCI_692821 : Nat.Prime 692821 := by norm_num

private theorem prime_eightyNineCI_734203 : Nat.Prime 734203 := by norm_num

private theorem prime_eightyNineCI_747863 : Nat.Prime 747863 := by norm_num

private theorem prime_eightyNineCI_815251 : Nat.Prime 815251 := by norm_num

private theorem prime_eightyNineCI_815819 : Nat.Prime 815819 := by norm_num

private theorem prime_eightyNineCI_868271 : Nat.Prime 868271 := by norm_num

private theorem prime_eightyNineCI_870601 : Nat.Prime 870601 := by norm_num

private theorem prime_eightyNineCI_871919 : Nat.Prime 871919 := by norm_num

private theorem prime_eightyNineCI_896047 : Nat.Prime 896047 := by norm_num

private theorem prime_eightyNineCI_903527 : Nat.Prime 903527 := by norm_num

private theorem prime_eightyNineCI_948469 : Nat.Prime 948469 := by norm_num

private theorem prime_eightyNineCI_1011509 : Nat.Prime 1011509 := by norm_num

private theorem prime_eightyNineCI_1018057 : Nat.Prime 1018057 := by norm_num

private theorem prime_eightyNineCI_1032847 : Nat.Prime 1032847 := by norm_num

private theorem prime_eightyNineCI_1083559 : Nat.Prime 1083559 := by norm_num

private theorem prime_eightyNineCI_1168969 : Nat.Prime 1168969 := by norm_num

private theorem prime_eightyNineCI_1198297 : Nat.Prime 1198297 := by norm_num

private theorem prime_eightyNineCI_1253897 : Nat.Prime 1253897 := by norm_num

private theorem prime_eightyNineCI_1298291 : Nat.Prime 1298291 := by norm_num

private theorem prime_eightyNineCI_1418051 : Nat.Prime 1418051 := by norm_num

private theorem prime_eightyNineCI_1479589 : Nat.Prime 1479589 := by norm_num

private theorem prime_eightyNineCI_1497511 : Nat.Prime 1497511 := by norm_num

private theorem prime_eightyNineCI_1497521 : Nat.Prime 1497521 := by norm_num

private theorem prime_eightyNineCI_1498829 : Nat.Prime 1498829 := by norm_num

private theorem prime_eightyNineCI_1535861 : Nat.Prime 1535861 := by norm_num

private theorem prime_eightyNineCI_1536907 : Nat.Prime 1536907 := by norm_num

private theorem prime_eightyNineCI_1538057 : Nat.Prime 1538057 := by norm_num

private theorem prime_eightyNineCI_1557137 : Nat.Prime 1557137 := by norm_num

private theorem prime_eightyNineCI_1615199 : Nat.Prime 1615199 := by norm_num

private theorem prime_eightyNineCI_1644497 : Nat.Prime 1644497 := by norm_num

private theorem prime_eightyNineCI_1736689 : Nat.Prime 1736689 := by norm_num

private theorem prime_eightyNineCI_1799801 : Nat.Prime 1799801 := by norm_num

private theorem prime_eightyNineCI_1813081 : Nat.Prime 1813081 := by norm_num

private theorem prime_eightyNineCI_1901027 : Nat.Prime 1901027 := by norm_num

private theorem prime_eightyNineCI_1914139 : Nat.Prime 1914139 := by norm_num

private theorem prime_eightyNineCI_2009857 : Nat.Prime 2009857 := by norm_num

private theorem prime_eightyNineCI_2202433 : Nat.Prime 2202433 := by norm_num

private theorem prime_eightyNineCI_2223631 : Nat.Prime 2223631 := by norm_num

private theorem prime_eightyNineCI_2273807 : Nat.Prime 2273807 := by norm_num

private theorem prime_eightyNineCI_2368297 : Nat.Prime 2368297 := by norm_num

private theorem prime_eightyNineCI_2411957 : Nat.Prime 2411957 := by norm_num

private theorem prime_eightyNineCI_2502443 : Nat.Prime 2502443 := by norm_num

private theorem prime_eightyNineCI_2764649 : Nat.Prime 2764649 := by norm_num

private theorem prime_eightyNineCI_2843671 : Nat.Prime 2843671 := by norm_num

private theorem prime_eightyNineCI_3108751 : Nat.Prime 3108751 := by norm_num

private theorem prime_eightyNineCI_3177203 : Nat.Prime 3177203 := by norm_num

private theorem prime_eightyNineCI_3181681 : Nat.Prime 3181681 := by norm_num

private theorem prime_eightyNineCI_3276103 : Nat.Prime 3276103 := by norm_num

private theorem prime_eightyNineCI_3387931 : Nat.Prime 3387931 := by norm_num

private theorem prime_eightyNineCI_3532541 : Nat.Prime 3532541 := by norm_num

private theorem prime_eightyNineCI_3693169 : Nat.Prime 3693169 := by norm_num

private theorem prime_eightyNineCI_3705773 : Nat.Prime 3705773 := by norm_num

private theorem prime_eightyNineCI_3717533 : Nat.Prime 3717533 := by norm_num

private theorem prime_eightyNineCI_4007239 : Nat.Prime 4007239 := by norm_num

private theorem prime_eightyNineCI_4073197 : Nat.Prime 4073197 := by norm_num

private theorem prime_eightyNineCI_4306891 : Nat.Prime 4306891 := by norm_num

private theorem prime_eightyNineCI_4307603 : Nat.Prime 4307603 := by norm_num

private theorem prime_eightyNineCI_4390453 : Nat.Prime 4390453 := by norm_num

private theorem prime_eightyNineCI_4409917 : Nat.Prime 4409917 := by norm_num

private theorem prime_eightyNineCI_4674127 : Nat.Prime 4674127 := by norm_num

private theorem prime_eightyNineCI_4856309 : Nat.Prime 4856309 := by norm_num

private theorem prime_eightyNineCI_5203391 : Nat.Prime 5203391 := by norm_num

private theorem prime_eightyNineCI_5368169 : Nat.Prime 5368169 := by norm_num

private theorem prime_eightyNineCI_5380079 : Nat.Prime 5380079 := by norm_num

private theorem prime_eightyNineCI_5441633 : Nat.Prime 5441633 := by norm_num

private theorem prime_eightyNineCI_5657261 : Nat.Prime 5657261 := by norm_num

private theorem prime_eightyNineCI_6177221 : Nat.Prime 6177221 := by norm_num

private theorem prime_eightyNineCI_6194819 : Nat.Prime 6194819 := by norm_num

private theorem prime_eightyNineCI_6773189 : Nat.Prime 6773189 := by norm_num

private theorem prime_eightyNineCI_6990673 : Nat.Prime 6990673 := by norm_num

private theorem prime_eightyNineCI_7418557 : Nat.Prime 7418557 := by norm_num

private theorem prime_eightyNineCI_8179349 : Nat.Prime 8179349 := by norm_num

private theorem prime_eightyNineCI_8244811 : Nat.Prime 8244811 := by norm_num

private theorem prime_eightyNineCI_8678599 : Nat.Prime 8678599 := by norm_num

private theorem prime_eightyNineCI_9635579 : Nat.Prime 9635579 := by norm_num

private theorem prime_eightyNineCI_9756067 : Nat.Prime 9756067 := by norm_num

private theorem prime_eightyNineCI_9767761 : Nat.Prime 9767761 := by norm_num

private theorem prime_eightyNineCI_9957307 : Nat.Prime 9957307 := by norm_num

private theorem prime_eightyNineCI_11301457 : Nat.Prime 11301457 := by norm_num

private theorem prime_eightyNineCI_11509159 : Nat.Prime 11509159 := by norm_num

private theorem prime_eightyNineCI_11585941 : Nat.Prime 11585941 := by norm_num

private theorem prime_eightyNineCI_11906729 : Nat.Prime 11906729 := by norm_num

private theorem prime_eightyNineCI_11981971 : Nat.Prime 11981971 := by norm_num

private theorem prime_eightyNineCI_12777629 : Nat.Prime 12777629 := by norm_num

private theorem prime_eightyNineCI_13037279 : Nat.Prime 13037279 := by norm_num

private theorem prime_eightyNineCI_13639993 : Nat.Prime 13639993 := by norm_num

private theorem prime_eightyNineCI_14314709 : Nat.Prime 14314709 := by norm_num

private theorem prime_eightyNineCI_15234101 : Nat.Prime 15234101 := by norm_num

private theorem prime_eightyNineCI_16992323 : Nat.Prime 16992323 := by norm_num

private theorem prime_eightyNineCI_17093123 : Nat.Prime 17093123 := by norm_num

private theorem prime_eightyNineCI_17248393 : Nat.Prime 17248393 := by norm_num

private theorem prime_eightyNineCI_17612711 : Nat.Prime 17612711 := by norm_num

private theorem prime_eightyNineCI_18233287 : Nat.Prime 18233287 := by norm_num

private theorem prime_eightyNineCI_19460569 : Nat.Prime 19460569 := by norm_num

private theorem prime_eightyNineCI_20130293 : Nat.Prime 20130293 := by norm_num

private theorem prime_eightyNineCI_20257271 : Nat.Prime 20257271 := by norm_num

private theorem prime_eightyNineCI_20390197 : Nat.Prime 20390197 := by norm_num

private theorem prime_eightyNineCI_20569403 : Nat.Prime 20569403 := by norm_num

private theorem prime_eightyNineCI_20997139 : Nat.Prime 20997139 := by norm_num

private theorem prime_eightyNineCI_21418183 : Nat.Prime 21418183 := by norm_num

private theorem prime_eightyNineCI_24128591 : Nat.Prime 24128591 := by norm_num

private theorem prime_eightyNineCI_24780863 : Nat.Prime 24780863 := by norm_num

private theorem prime_eightyNineCI_28047757 : Nat.Prime 28047757 := by norm_num

private theorem prime_eightyNineCI_28669231 : Nat.Prime 28669231 := by norm_num

private theorem prime_eightyNineCI_29030941 : Nat.Prime 29030941 := by norm_num

private theorem prime_eightyNineCI_30411569 : Nat.Prime 30411569 := by
  apply lucas_primality 30411569 (3 : ZMod 30411569)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (67, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (67, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) = 30411569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_67
      · exact prime_eightyNineCI_2579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30411569) ^ 15205784 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30411569) ^ 2764688 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30411569) ^ 453904 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 30411569) ^ 11792 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_30468203 : Nat.Prime 30468203 := by
  apply lucas_primality 30468203 (2 : ZMod 30468203)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15234101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15234101, 1)] : List FactorBlock).map factorBlockValue).prod) = 30468203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_15234101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30468203) ^ 15234101 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30468203) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_32761031 : Nat.Prime 32761031 := by
  apply lucas_primality 32761031 (7 : ZMod 32761031)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3276103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3276103, 1)] : List FactorBlock).map factorBlockValue).prod) = 32761031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_3276103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 32761031) ^ 16380515 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 32761031) ^ 6552206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 32761031) ^ 10 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_35225423 : Nat.Prime 35225423 := by
  apply lucas_primality 35225423 (5 : ZMod 35225423)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17612711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17612711, 1)] : List FactorBlock).map factorBlockValue).prod) = 35225423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17612711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 35225423) ^ 17612711 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 35225423) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_38713949 : Nat.Prime 38713949 := by
  apply lucas_primality 38713949 (3 : ZMod 38713949)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (106357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (106357, 1)] : List FactorBlock).map factorBlockValue).prod) = 38713949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_106357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38713949) ^ 19356974 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 38713949) ^ 5530564 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 38713949) ^ 2977996 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 38713949) ^ 364 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_39572567 : Nat.Prime 39572567 := by
  apply lucas_primality 39572567 (5 : ZMod 39572567)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (17, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (17, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod) = 39572567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39572567) ^ 19786283 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 39572567) ^ 3597506 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 39572567) ^ 2327798 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 39572567) ^ 4114 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_40514543 : Nat.Prime 40514543 := by
  apply lucas_primality 40514543 (5 : ZMod 40514543)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20257271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20257271, 1)] : List FactorBlock).map factorBlockValue).prod) = 40514543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_20257271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 40514543) ^ 20257271 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 40514543) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_41138807 : Nat.Prime 41138807 := by
  apply lucas_primality 41138807 (5 : ZMod 41138807)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20569403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20569403, 1)] : List FactorBlock).map factorBlockValue).prod) = 41138807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_20569403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 41138807) ^ 20569403 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 41138807) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_41432249 : Nat.Prime 41432249 := by
  apply lucas_primality 41432249 (3 : ZMod 41432249)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (36217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (36217, 1)] : List FactorBlock).map factorBlockValue).prod) = 41432249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_36217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41432249) ^ 20716124 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 41432249) ^ 3766568 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 41432249) ^ 3187096 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 41432249) ^ 1144 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_44198459 : Nat.Prime 44198459 := by
  apply lucas_primality 44198459 (2 : ZMod 44198459)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1669, 1), (13241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1669, 1), (13241, 1)] : List FactorBlock).map factorBlockValue).prod) = 44198459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_1669
      · exact prime_eightyNineCI_13241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44198459) ^ 22099229 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44198459) ^ 26482 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44198459) ^ 3338 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_45205829 : Nat.Prime 45205829 := by
  apply lucas_primality 45205829 (2 : ZMod 45205829)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11301457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11301457, 1)] : List FactorBlock).map factorBlockValue).prod) = 45205829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11301457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45205829) ^ 22602914 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45205829) ^ 4 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_47395297 : Nat.Prime 47395297 := by
  apply lucas_primality 47395297 (7 : ZMod 47395297)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (13, 1), (12659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (13, 1), (12659, 1)] : List FactorBlock).map factorBlockValue).prod) = 47395297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_12659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47395297) ^ 23697648 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47395297) ^ 15798432 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47395297) ^ 3645792 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47395297) ^ 3744 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_47657689 : Nat.Prime 47657689 := by
  apply lucas_primality 47657689 (11 : ZMod 47657689)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (103, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (103, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 47657689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_103
      · exact prime_eightyNineCI_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47657689) ^ 23828844 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 47657689) ^ 15885896 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 47657689) ^ 3665976 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 47657689) ^ 462696 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 47657689) ^ 32136 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_47965273 : Nat.Prime 47965273 := by
  apply lucas_primality 47965273 (7 : ZMod 47965273)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (293, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (293, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 47965273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_293
      · exact prime_eightyNineCI_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47965273) ^ 23982636 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47965273) ^ 15988424 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47965273) ^ 2524488 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47965273) ^ 163704 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 47965273) ^ 133608 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_55803719 : Nat.Prime 55803719 := by
  apply lucas_primality 55803719 (11 : ZMod 55803719)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (167077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (167077, 1)] : List FactorBlock).map factorBlockValue).prod) = 55803719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_167
      · exact prime_eightyNineCI_167077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 55803719) ^ 27901859 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 55803719) ^ 334154 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 55803719) ^ 334 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_58196849 : Nat.Prime 58196849 := by
  apply lucas_primality 58196849 (3 : ZMod 58196849)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (19, 1), (11261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (19, 1), (11261, 1)] : List FactorBlock).map factorBlockValue).prod) = 58196849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_11261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58196849) ^ 29098424 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 58196849) ^ 3423344 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 58196849) ^ 3062992 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 58196849) ^ 5168 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_71534773 : Nat.Prime 71534773 := by
  apply lucas_primality 71534773 (2 : ZMod 71534773)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (71, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (71, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 71534773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71534773) ^ 35767386 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71534773) ^ 23844924 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71534773) ^ 3764988 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71534773) ^ 1007532 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 71534773) ^ 145692 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_73089353 : Nat.Prime 73089353 := by
  apply lucas_primality 73089353 (3 : ZMod 73089353)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (73, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (73, 1), (941, 1)] : List FactorBlock).map factorBlockValue).prod) = 73089353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73089353) ^ 36544676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 73089353) ^ 10441336 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 73089353) ^ 3846808 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 73089353) ^ 1001224 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 73089353) ^ 77672 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_76497913 : Nat.Prime 76497913 := by
  apply lucas_primality 76497913 (10 : ZMod 76497913)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (79, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (79, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) = 76497913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_79
      · exact prime_eightyNineCI_4483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 76497913) ^ 38248956 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 76497913) ^ 25499304 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 76497913) ^ 968328 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 76497913) ^ 17064 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_80833187 : Nat.Prime 80833187 := by
  apply lucas_primality 80833187 (2 : ZMod 80833187)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (97861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (97861, 1)] : List FactorBlock).map factorBlockValue).prod) = 80833187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_59
      · exact prime_eightyNineCI_97861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80833187) ^ 40416593 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80833187) ^ 11547598 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80833187) ^ 1370054 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80833187) ^ 826 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_81305113 : Nat.Prime 81305113 := by
  apply lucas_primality 81305113 (5 : ZMod 81305113)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (47, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (47, 1), (1471, 1)] : List FactorBlock).map factorBlockValue).prod) = 81305113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_47
      · exact prime_eightyNineCI_1471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 81305113) ^ 40652556 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 81305113) ^ 27101704 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 81305113) ^ 11615016 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 81305113) ^ 1729896 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 81305113) ^ 55272 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_82211329 : Nat.Prime 82211329 := by
  apply lucas_primality 82211329 (11 : ZMod 82211329)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (19, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (19, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 82211329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 82211329) ^ 41105664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 82211329) ^ 27403776 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 82211329) ^ 4326912 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 82211329) ^ 262656 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_82295723 : Nat.Prime 82295723 := by
  apply lucas_primality 82295723 (2 : ZMod 82295723)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (79, 1), (12113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (79, 1), (12113, 1)] : List FactorBlock).map factorBlockValue).prod) = 82295723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_79
      · exact prime_eightyNineCI_12113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82295723) ^ 41147861 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 82295723) ^ 1913854 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 82295723) ^ 1041718 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 82295723) ^ 6794 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_82434491 : Nat.Prime 82434491 := by
  apply lucas_primality 82434491 (6 : ZMod 82434491)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (487, 1), (16927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (487, 1), (16927, 1)] : List FactorBlock).map factorBlockValue).prod) = 82434491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_487
      · exact prime_eightyNineCI_16927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 82434491) ^ 41217245 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 82434491) ^ 16486898 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 82434491) ^ 169270 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 82434491) ^ 4870 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_89645399 : Nat.Prime 89645399 := by
  apply lucas_primality 89645399 (14 : ZMod 89645399)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (84731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (84731, 1)] : List FactorBlock).map factorBlockValue).prod) = 89645399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_84731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 89645399) ^ 44822699 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 89645399) ^ 3897626 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 89645399) ^ 1058 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_92634953 : Nat.Prime 92634953 := by
  apply lucas_primality 92634953 (3 : ZMod 92634953)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1523, 1), (7603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1523, 1), (7603, 1)] : List FactorBlock).map factorBlockValue).prod) = 92634953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_1523
      · exact prime_eightyNineCI_7603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 92634953) ^ 46317476 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 92634953) ^ 60824 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 92634953) ^ 12184 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_102761783 : Nat.Prime 102761783 := by
  apply lucas_primality 102761783 (5 : ZMod 102761783)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (375043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (375043, 1)] : List FactorBlock).map factorBlockValue).prod) = 102761783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_137
      · exact prime_eightyNineCI_375043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 102761783) ^ 51380891 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 102761783) ^ 750086 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 102761783) ^ 274 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_111997679 : Nat.Prime 111997679 := by
  apply lucas_primality 111997679 (29 : ZMod 111997679)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4307603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4307603, 1)] : List FactorBlock).map factorBlockValue).prod) = 111997679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_4307603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 111997679) ^ 55998839 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 111997679) ^ 8615206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 111997679) ^ 26 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_144006769 : Nat.Prime 144006769 := by
  apply lucas_primality 144006769 (17 : ZMod 144006769)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (333349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (333349, 1)] : List FactorBlock).map factorBlockValue).prod) = 144006769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_333349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 144006769) ^ 72003384 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 144006769) ^ 48002256 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 144006769) ^ 432 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_153252667 : Nat.Prime 153252667 := by
  apply lucas_primality 153252667 (2 : ZMod 153252667)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (743, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (743, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 153252667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_743
      · exact prime_eightyNineCI_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153252667) ^ 76626333 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 153252667) ^ 51084222 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 153252667) ^ 21893238 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 153252667) ^ 206262 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 153252667) ^ 93618 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_163248991 : Nat.Prime 163248991 := by
  apply lucas_primality 163248991 (6 : ZMod 163248991)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5441633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5441633, 1)] : List FactorBlock).map factorBlockValue).prod) = 163248991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_5441633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 163248991) ^ 81624495 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 163248991) ^ 54416330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 163248991) ^ 32649798 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 163248991) ^ 30 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_172886083 : Nat.Prime 172886083 := by
  apply lucas_primality 172886083 (5 : ZMod 172886083)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (172541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (172541, 1)] : List FactorBlock).map factorBlockValue).prod) = 172886083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_167
      · exact prime_eightyNineCI_172541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 172886083) ^ 86443041 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 172886083) ^ 57628694 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 172886083) ^ 1035246 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 172886083) ^ 1002 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_192357761 : Nat.Prime 192357761 := by
  apply lucas_primality 192357761 (11 : ZMod 192357761)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (42937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (42937, 1)] : List FactorBlock).map factorBlockValue).prod) = 192357761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_42937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 192357761) ^ 96178880 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 192357761) ^ 38471552 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 192357761) ^ 27479680 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 192357761) ^ 4480 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_194277437 : Nat.Prime 194277437 := by
  apply lucas_primality 194277437 (2 : ZMod 194277437)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (61, 1), (83, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (61, 1), (83, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 194277437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_53
      · exact prime_eightyNineCI_61
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 194277437) ^ 97138718 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 194277437) ^ 3665612 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 194277437) ^ 3184876 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 194277437) ^ 2340692 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 194277437) ^ 1073356 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_206980717 : Nat.Prime 206980717 := by
  apply lucas_primality 206980717 (2 : ZMod 206980717)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17248393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17248393, 1)] : List FactorBlock).map factorBlockValue).prod) = 206980717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_17248393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 206980717) ^ 103490358 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 206980717) ^ 68993572 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 206980717) ^ 12 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_209231003 : Nat.Prime 209231003 := by
  apply lucas_primality 209231003 (2 : ZMod 209231003)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (419, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (419, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 209231003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_419
      · exact prime_eightyNineCI_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 209231003) ^ 104615501 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209231003) ^ 12307706 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209231003) ^ 11012158 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209231003) ^ 499358 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209231003) ^ 270674 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_210148457 : Nat.Prime 210148457 := by
  apply lucas_primality 210148457 (3 : ZMod 210148457)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (37, 1), (14489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (37, 1), (14489, 1)] : List FactorBlock).map factorBlockValue).prod) = 210148457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_37
      · exact prime_eightyNineCI_14489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 210148457) ^ 105074228 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 210148457) ^ 30021208 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 210148457) ^ 5679688 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 210148457) ^ 14504 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_215009843 : Nat.Prime 215009843 := by
  apply lucas_primality 215009843 (2 : ZMod 215009843)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4674127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4674127, 1)] : List FactorBlock).map factorBlockValue).prod) = 215009843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_4674127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215009843) ^ 107504921 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 215009843) ^ 9348254 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 215009843) ^ 46 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_233272541 : Nat.Prime 233272541 := by
  apply lucas_primality 233272541 (3 : ZMod 233272541)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (367, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (367, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 233272541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_61
      · exact prime_eightyNineCI_367
      · exact prime_eightyNineCI_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 233272541) ^ 116636270 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233272541) ^ 46654508 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233272541) ^ 3824140 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233272541) ^ 635620 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 233272541) ^ 447740 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_237435403 : Nat.Prime 237435403 := by
  apply lucas_primality 237435403 (5 : ZMod 237435403)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39572567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39572567, 1)] : List FactorBlock).map factorBlockValue).prod) = 237435403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_39572567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 237435403) ^ 118717701 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 237435403) ^ 79145134 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 237435403) ^ 6 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_314531573 : Nat.Prime 314531573 := by
  apply lucas_primality 314531573 (2 : ZMod 314531573)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6703, 1), (11731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6703, 1), (11731, 1)] : List FactorBlock).map factorBlockValue).prod) = 314531573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_6703
      · exact prime_eightyNineCI_11731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 314531573) ^ 157265786 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 314531573) ^ 46924 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 314531573) ^ 26812 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_315860983 : Nat.Prime 315860983 := by
  apply lucas_primality 315860983 (6 : ZMod 315860983)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (83, 1), (21871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (83, 1), (21871, 1)] : List FactorBlock).map factorBlockValue).prod) = 315860983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_29
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_21871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 315860983) ^ 157930491 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 315860983) ^ 105286994 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 315860983) ^ 10891758 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 315860983) ^ 3805554 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 315860983) ^ 14442 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_326243153 : Nat.Prime 326243153 := by
  apply lucas_primality 326243153 (3 : ZMod 326243153)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20390197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20390197, 1)] : List FactorBlock).map factorBlockValue).prod) = 326243153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_20390197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 326243153) ^ 163121576 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 326243153) ^ 16 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_340741031 : Nat.Prime 340741031 := by
  apply lucas_primality 340741031 (7 : ZMod 340741031)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (43, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (43, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 340741031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 340741031) ^ 170370515 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 340741031) ^ 68148206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 340741031) ^ 48677290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 340741031) ^ 20043590 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 340741031) ^ 7924210 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 340741031) ^ 51170 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_346273399 : Nat.Prime 346273399 := by
  apply lucas_primality 346273399 (3 : ZMod 346273399)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (663359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (663359, 1)] : List FactorBlock).map factorBlockValue).prod) = 346273399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_29
      · exact prime_eightyNineCI_663359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 346273399) ^ 173136699 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 346273399) ^ 115424466 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 346273399) ^ 11940462 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 346273399) ^ 522 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_351432239 : Nat.Prime 351432239 := by
  apply lucas_primality 351432239 (7 : ZMod 351432239)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (163, 1), (26293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (163, 1), (26293, 1)] : List FactorBlock).map factorBlockValue).prod) = 351432239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_163
      · exact prime_eightyNineCI_26293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 351432239) ^ 175716119 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 351432239) ^ 8571518 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 351432239) ^ 2156026 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 351432239) ^ 13366 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_360435497 : Nat.Prime 360435497 := by
  apply lucas_primality 360435497 (3 : ZMod 360435497)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (131, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (131, 1), (20231, 1)] : List FactorBlock).map factorBlockValue).prod) = 360435497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_20231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 360435497) ^ 180217748 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 360435497) ^ 21202088 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 360435497) ^ 2751416 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 360435497) ^ 17816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_385689503 : Nat.Prime 385689503 := by
  apply lucas_primality 385689503 (5 : ZMod 385689503)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (604529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (604529, 1)] : List FactorBlock).map factorBlockValue).prod) = 385689503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_29
      · exact prime_eightyNineCI_604529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 385689503) ^ 192844751 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385689503) ^ 35062682 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385689503) ^ 13299638 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 385689503) ^ 638 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_392426599 : Nat.Prime 392426599 := by
  apply lucas_primality 392426599 (3 : ZMod 392426599)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2843671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2843671, 1)] : List FactorBlock).map factorBlockValue).prod) = 392426599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_2843671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 392426599) ^ 196213299 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 392426599) ^ 130808866 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 392426599) ^ 17062026 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 392426599) ^ 138 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_397369901 : Nat.Prime 397369901 := by
  apply lucas_primality 397369901 (3 : ZMod 397369901)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (233747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (233747, 1)] : List FactorBlock).map factorBlockValue).prod) = 397369901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_233747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 397369901) ^ 198684950 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 397369901) ^ 79473980 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 397369901) ^ 23374700 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 397369901) ^ 1700 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_397873897 : Nat.Prime 397873897 := by
  apply lucas_primality 397873897 (5 : ZMod 397873897)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2368297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2368297, 1)] : List FactorBlock).map factorBlockValue).prod) = 397873897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_2368297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 397873897) ^ 198936948 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 397873897) ^ 132624632 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 397873897) ^ 56839128 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 397873897) ^ 168 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_421442459 : Nat.Prime 421442459 := by
  apply lucas_primality 421442459 (2 : ZMod 421442459)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (131, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (131, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 421442459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421442459) ^ 210721229 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 421442459) ^ 22181182 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 421442459) ^ 13594918 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 421442459) ^ 3217118 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 421442459) ^ 154318 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_429776993 : Nat.Prime 429776993 := by
  apply lucas_primality 429776993 (3 : ZMod 429776993)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3571, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3571, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) = 429776993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3571
      · exact prime_eightyNineCI_3761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 429776993) ^ 214888496 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 429776993) ^ 120352 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 429776993) ^ 114272 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_442434067 : Nat.Prime 442434067 := by
  apply lucas_primality 442434067 (2 : ZMod 442434067)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (305971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (305971, 1)] : List FactorBlock).map factorBlockValue).prod) = 442434067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_241
      · exact prime_eightyNineCI_305971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 442434067) ^ 221217033 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 442434067) ^ 147478022 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 442434067) ^ 1835826 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 442434067) ^ 1446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_462772799 : Nat.Prime 462772799 := by
  apply lucas_primality 462772799 (11 : ZMod 462772799)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (1063, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (1063, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) = 462772799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_109
      · exact prime_eightyNineCI_1063
      · exact prime_eightyNineCI_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 462772799) ^ 231386399 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 462772799) ^ 4245622 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 462772799) ^ 435346 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 462772799) ^ 231734 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_466545083 : Nat.Prime 466545083 := by
  apply lucas_primality 466545083 (2 : ZMod 466545083)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233272541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233272541, 1)] : List FactorBlock).map factorBlockValue).prod) = 466545083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_233272541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 466545083) ^ 233272541 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 466545083) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_524604593 : Nat.Prime 524604593 := by
  apply lucas_primality 524604593 (3 : ZMod 524604593)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (677, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (677, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) = 524604593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_677
      · exact prime_eightyNineCI_2549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 524604593) ^ 262302296 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 524604593) ^ 27610768 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 524604593) ^ 774896 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 524604593) ^ 205808 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_527953457 : Nat.Prime 527953457 := by
  apply lucas_primality 527953457 (3 : ZMod 527953457)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (1736689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (1736689, 1)] : List FactorBlock).map factorBlockValue).prod) = 527953457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_1736689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 527953457) ^ 263976728 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 527953457) ^ 27787024 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 527953457) ^ 304 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_541995287 : Nat.Prime 541995287 := by
  apply lucas_primality 541995287 (5 : ZMod 541995287)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (38713949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (38713949, 1)] : List FactorBlock).map factorBlockValue).prod) = 541995287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_38713949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 541995287) ^ 270997643 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 541995287) ^ 77427898 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 541995287) ^ 14 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_609796679 : Nat.Prime 609796679 := by
  apply lucas_primality 609796679 (7 : ZMod 609796679)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (419, 1), (38299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (419, 1), (38299, 1)] : List FactorBlock).map factorBlockValue).prod) = 609796679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_419
      · exact prime_eightyNineCI_38299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 609796679) ^ 304898339 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 609796679) ^ 32094562 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 609796679) ^ 1455362 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 609796679) ^ 15922 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_705855851 : Nat.Prime 705855851 := by
  apply lucas_primality 705855851 (2 : ZMod 705855851)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (739, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (739, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) = 705855851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_739
      · exact prime_eightyNineCI_2729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 705855851) ^ 352927925 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 705855851) ^ 141171170 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 705855851) ^ 100836550 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 705855851) ^ 955150 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 705855851) ^ 258650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_781252067 : Nat.Prime 781252067 := by
  apply lucas_primality 781252067 (2 : ZMod 781252067)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (55803719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (55803719, 1)] : List FactorBlock).map factorBlockValue).prod) = 781252067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_55803719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 781252067) ^ 390626033 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 781252067) ^ 111607438 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 781252067) ^ 14 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_819337889 : Nat.Prime 819337889 := by
  apply lucas_primality 819337889 (3 : ZMod 819337889)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (149, 1), (239, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (149, 1), (239, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 819337889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_149
      · exact prime_eightyNineCI_239
      · exact prime_eightyNineCI_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 819337889) ^ 409668944 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 819337889) ^ 5498912 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 819337889) ^ 3428192 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 819337889) ^ 1139552 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_955965833 : Nat.Prime 955965833 := by
  apply lucas_primality 955965833 (3 : ZMod 955965833)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (821, 1), (145549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (821, 1), (145549, 1)] : List FactorBlock).map factorBlockValue).prod) = 955965833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_821
      · exact prime_eightyNineCI_145549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 955965833) ^ 477982916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 955965833) ^ 1164392 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 955965833) ^ 6568 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_982365317 : Nat.Prime 982365317 := by
  apply lucas_primality 982365317 (2 : ZMod 982365317)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (3108751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (3108751, 1)] : List FactorBlock).map factorBlockValue).prod) = 982365317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_79
      · exact prime_eightyNineCI_3108751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 982365317) ^ 491182658 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 982365317) ^ 12435004 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 982365317) ^ 316 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1110175771 : Nat.Prime 1110175771 := by
  apply lucas_primality 1110175771 (14 : ZMod 1110175771)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (197, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (197, 1), (17077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110175771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_197
      · exact prime_eightyNineCI_17077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1110175771) ^ 555087885 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1110175771) ^ 370058590 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1110175771) ^ 222035154 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1110175771) ^ 100925070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1110175771) ^ 5635410 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 1110175771) ^ 65010 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1131928537 : Nat.Prime 1131928537 := by
  apply lucas_primality 1131928537 (5 : ZMod 1131928537)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (587, 1), (80347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (587, 1), (80347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1131928537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_587
      · exact prime_eightyNineCI_80347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1131928537) ^ 565964268 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1131928537) ^ 377309512 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1131928537) ^ 1928328 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1131928537) ^ 14088 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1137487129 : Nat.Prime 1137487129 := by
  apply lucas_primality 1137487129 (17 : ZMod 1137487129)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47395297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47395297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137487129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_47395297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 1137487129) ^ 568743564 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1137487129) ^ 379162376 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1137487129) ^ 24 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1149986611 : Nat.Prime 1149986611 := by
  apply lucas_primality 1149986611 (2 : ZMod 1149986611)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (12777629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (12777629, 1)] : List FactorBlock).map factorBlockValue).prod) = 1149986611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_12777629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1149986611) ^ 574993305 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149986611) ^ 383328870 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149986611) ^ 229997322 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1149986611) ^ 90 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1166859443 : Nat.Prime 1166859443 := by
  apply lucas_primality 1166859443 (2 : ZMod 1166859443)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11906729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11906729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166859443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11906729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1166859443) ^ 583429721 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166859443) ^ 166694206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166859443) ^ 98 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1603747031 : Nat.Prime 1603747031 := by
  apply lucas_primality 1603747031 (17 : ZMod 1603747031)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (1498829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (1498829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603747031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_107
      · exact prime_eightyNineCI_1498829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1603747031) ^ 801873515 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1603747031) ^ 320749406 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1603747031) ^ 14988290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1603747031) ^ 1070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1691874157 : Nat.Prime 1691874157 := by
  apply lucas_primality 1691874157 (5 : ZMod 1691874157)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (107, 1), (26891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (107, 1), (26891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691874157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_107
      · exact prime_eightyNineCI_26891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1691874157) ^ 845937078 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1691874157) ^ 563958052 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1691874157) ^ 241696308 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1691874157) ^ 15811908 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1691874157) ^ 62916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1911778769 : Nat.Prime 1911778769 := by
  apply lucas_primality 1911778769 (3 : ZMod 1911778769)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (47, 1), (110533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (47, 1), (110533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1911778769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_47
      · exact prime_eightyNineCI_110533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1911778769) ^ 955889384 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1911778769) ^ 83120816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1911778769) ^ 40676144 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1911778769) ^ 17296 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1981463581 : Nat.Prime 1981463581 := by
  apply lucas_primality 1981463581 (7 : ZMod 1981463581)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (31, 1), (41, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (31, 1), (41, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1981463581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_2887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1981463581) ^ 990731790 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1981463581) ^ 660487860 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1981463581) ^ 396292716 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1981463581) ^ 63918180 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1981463581) ^ 48328380 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1981463581) ^ 686340 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2148485147 : Nat.Prime 2148485147 := by
  apply lucas_primality 2148485147 (2 : ZMod 2148485147)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3307, 1), (324839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3307, 1), (324839, 1)] : List FactorBlock).map factorBlockValue).prod) = 2148485147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3307
      · exact prime_eightyNineCI_324839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2148485147) ^ 1074242573 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148485147) ^ 649678 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148485147) ^ 6614 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2217303731 : Nat.Prime 2217303731 := by
  apply lucas_primality 2217303731 (2 : ZMod 2217303731)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (71, 1), (135781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (71, 1), (135781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2217303731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_135781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2217303731) ^ 1108651865 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217303731) ^ 443460746 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217303731) ^ 96404510 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217303731) ^ 31229630 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217303731) ^ 16330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2311939579 : Nat.Prime 2311939579 := by
  apply lucas_primality 2311939579 (10 : ZMod 2311939579)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4783, 1), (6197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4783, 1), (6197, 1)] : List FactorBlock).map factorBlockValue).prod) = 2311939579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_4783
      · exact prime_eightyNineCI_6197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2311939579) ^ 1155969789 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2311939579) ^ 770646526 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2311939579) ^ 177841506 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2311939579) ^ 483366 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2311939579) ^ 373074 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2566386451 : Nat.Prime 2566386451 := by
  apply lucas_primality 2566386451 (3 : ZMod 2566386451)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (1901027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (1901027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2566386451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_1901027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2566386451) ^ 1283193225 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2566386451) ^ 855462150 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2566386451) ^ 513277290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2566386451) ^ 1350 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2567095093 : Nat.Prime 2567095093 := by
  apply lucas_primality 2567095093 (2 : ZMod 2567095093)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (19, 1), (417007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (19, 1), (417007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2567095093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_417007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2567095093) ^ 1283547546 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2567095093) ^ 855698364 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2567095093) ^ 135110268 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2567095093) ^ 6156 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2666527189 : Nat.Prime 2666527189 := by
  apply lucas_primality 2666527189 (2 : ZMod 2666527189)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17093123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17093123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2666527189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_17093123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2666527189) ^ 1333263594 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2666527189) ^ 888842396 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2666527189) ^ 205117476 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2666527189) ^ 156 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2766177329 : Nat.Prime 2766177329 := by
  apply lucas_primality 2766177329 (3 : ZMod 2766177329)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (172886083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (172886083, 1)] : List FactorBlock).map factorBlockValue).prod) = 2766177329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_172886083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2766177329) ^ 1383088664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2766177329) ^ 16 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2935118339 : Nat.Prime 2935118339 := by
  apply lucas_primality 2935118339 (2 : ZMod 2935118339)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (809, 1), (42187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (809, 1), (42187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2935118339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_809
      · exact prime_eightyNineCI_42187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2935118339) ^ 1467559169 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935118339) ^ 68258566 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935118339) ^ 3628082 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2935118339) ^ 69574 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2936344207 : Nat.Prime 2936344207 := by
  apply lucas_primality 2936344207 (3 : ZMod 2936344207)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (6194819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (6194819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2936344207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_79
      · exact prime_eightyNineCI_6194819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2936344207) ^ 1468172103 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2936344207) ^ 978781402 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2936344207) ^ 37168914 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2936344207) ^ 474 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3218785183 : Nat.Prime 3218785183 := by
  apply lucas_primality 3218785183 (5 : ZMod 3218785183)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (907, 1), (65719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (907, 1), (65719, 1)] : List FactorBlock).map factorBlockValue).prod) = 3218785183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_907
      · exact prime_eightyNineCI_65719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3218785183) ^ 1609392591 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3218785183) ^ 1072928394 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3218785183) ^ 3548826 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3218785183) ^ 48978 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3337586869 : Nat.Prime 3337586869 := by
  apply lucas_primality 3337586869 (2 : ZMod 3337586869)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (103, 1), (35069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (103, 1), (35069, 1)] : List FactorBlock).map factorBlockValue).prod) = 3337586869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_103
      · exact prime_eightyNineCI_35069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3337586869) ^ 1668793434 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3337586869) ^ 1112528956 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3337586869) ^ 476798124 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3337586869) ^ 303416988 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3337586869) ^ 32403756 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3337586869) ^ 95172 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3406525163 : Nat.Prime 3406525163 := by
  apply lucas_primality 3406525163 (2 : ZMod 3406525163)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (89645399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (89645399, 1)] : List FactorBlock).map factorBlockValue).prod) = 3406525163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_89645399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3406525163) ^ 1703262581 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3406525163) ^ 179290798 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3406525163) ^ 38 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3640599539 : Nat.Prime 3640599539 := by
  apply lucas_primality 3640599539 (2 : ZMod 3640599539)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (97, 1), (58099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (97, 1), (58099, 1)] : List FactorBlock).map factorBlockValue).prod) = 3640599539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_97
      · exact prime_eightyNineCI_58099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3640599539) ^ 1820299769 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640599539) ^ 214152914 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640599539) ^ 191610502 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640599539) ^ 37531954 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3640599539) ^ 62662 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3648184339 : Nat.Prime 3648184339 := by
  apply lucas_primality 3648184339 (3 : ZMod 3648184339)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (71, 1), (450727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (71, 1), (450727, 1)] : List FactorBlock).map factorBlockValue).prod) = 3648184339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_450727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3648184339) ^ 1824092169 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3648184339) ^ 1216061446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3648184339) ^ 192009702 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3648184339) ^ 51382878 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3648184339) ^ 8094 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3701280899 : Nat.Prime 3701280899 := by
  apply lucas_primality 3701280899 (2 : ZMod 3701280899)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (103, 1), (82799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (103, 1), (82799, 1)] : List FactorBlock).map factorBlockValue).prod) = 3701280899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_103
      · exact prime_eightyNineCI_82799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3701280899) ^ 1850640449 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3701280899) ^ 528754414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3701280899) ^ 119396158 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3701280899) ^ 35934766 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3701280899) ^ 44702 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3891805633 : Nat.Prime 3891805633 := by
  apply lucas_primality 3891805633 (10 : ZMod 3891805633)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (13, 1), (37, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (13, 1), (37, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3891805633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_37
      · exact prime_eightyNineCI_1277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3891805633) ^ 1945902816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 3891805633) ^ 1297268544 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 3891805633) ^ 353800512 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 3891805633) ^ 299369664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 3891805633) ^ 105183936 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 3891805633) ^ 3047616 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4443969043 : Nat.Prime 4443969043 := by
  apply lucas_primality 4443969043 (2 : ZMod 4443969043)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (82295723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (82295723, 1)] : List FactorBlock).map factorBlockValue).prod) = 4443969043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_82295723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4443969043) ^ 2221984521 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443969043) ^ 1481323014 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443969043) ^ 54 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4549948517 : Nat.Prime 4549948517 := by
  apply lucas_primality 4549948517 (2 : ZMod 4549948517)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1137487129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1137487129, 1)] : List FactorBlock).map factorBlockValue).prod) = 4549948517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_1137487129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4549948517) ^ 2274974258 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4549948517) ^ 4 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4894063121 : Nat.Prime 4894063121 := by
  apply lucas_primality 4894063121 (3 : ZMod 4894063121)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (193, 1), (197, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (193, 1), (197, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 4894063121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_193
      · exact prime_eightyNineCI_197
      · exact prime_eightyNineCI_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4894063121) ^ 2447031560 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4894063121) ^ 978812624 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4894063121) ^ 25357840 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4894063121) ^ 24842960 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4894063121) ^ 3041680 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_5371278907 : Nat.Prime 5371278907 := by
  apply lucas_primality 5371278907 (2 : ZMod 5371278907)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (4409917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (4409917, 1)] : List FactorBlock).map factorBlockValue).prod) = 5371278907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_29
      · exact prime_eightyNineCI_4409917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5371278907) ^ 2685639453 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5371278907) ^ 1790426302 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5371278907) ^ 767325558 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5371278907) ^ 185216514 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5371278907) ^ 1218 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_5482793983 : Nat.Prime 5482793983 := by
  apply lucas_primality 5482793983 (3 : ZMod 5482793983)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (67, 1), (439961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (67, 1), (439961, 1)] : List FactorBlock).map factorBlockValue).prod) = 5482793983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_67
      · exact prime_eightyNineCI_439961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5482793983) ^ 2741396991 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482793983) ^ 1827597994 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482793983) ^ 176864322 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482793983) ^ 81832746 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482793983) ^ 12462 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6619699231 : Nat.Prime 6619699231 := by
  apply lucas_primality 6619699231 (3 : ZMod 6619699231)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (383, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (383, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 6619699231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_37
      · exact prime_eightyNineCI_383
      · exact prime_eightyNineCI_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6619699231) ^ 3309849615 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 2206566410 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 1323939846 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 287813010 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 178910790 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 17283810 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 6619699231) ^ 9777990 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6865886449 : Nat.Prime 6865886449 := by
  apply lucas_primality 6865886449 (19 : ZMod 6865886449)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (1538057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (1538057, 1)] : List FactorBlock).map factorBlockValue).prod) = 6865886449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_1538057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 6865886449) ^ 3432943224 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 6865886449) ^ 2288628816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 6865886449) ^ 221480208 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 6865886449) ^ 4464 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7123062091 : Nat.Prime 7123062091 := by
  apply lucas_primality 7123062091 (2 : ZMod 7123062091)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (237435403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (237435403, 1)] : List FactorBlock).map factorBlockValue).prod) = 7123062091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_237435403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7123062091) ^ 3561531045 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7123062091) ^ 2374354030 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7123062091) ^ 1424612418 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7123062091) ^ 30 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7711070407 : Nat.Prime 7711070407 := by
  apply lucas_primality 7711070407 (3 : ZMod 7711070407)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1669, 1), (59233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1669, 1), (59233, 1)] : List FactorBlock).map factorBlockValue).prod) = 7711070407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_1669
      · exact prime_eightyNineCI_59233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7711070407) ^ 3855535203 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7711070407) ^ 2570356802 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7711070407) ^ 593159262 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7711070407) ^ 4620174 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 7711070407) ^ 130182 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7947398021 : Nat.Prime 7947398021 := by
  apply lucas_primality 7947398021 (2 : ZMod 7947398021)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (397369901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (397369901, 1)] : List FactorBlock).map factorBlockValue).prod) = 7947398021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_397369901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7947398021) ^ 3973699010 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7947398021) ^ 1589479604 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7947398021) ^ 20 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_9249833287 : Nat.Prime 9249833287 := by
  apply lucas_primality 9249833287 (3 : ZMod 9249833287)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 2), (92641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 2), (92641, 1)] : List FactorBlock).map factorBlockValue).prod) = 9249833287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_92641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9249833287) ^ 4624916643 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9249833287) ^ 3083277762 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9249833287) ^ 215112402 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 9249833287) ^ 99846 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_9264843911 : Nat.Prime 9264843911 := by
  apply lucas_primality 9264843911 (7 : ZMod 9264843911)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (73, 1), (1813081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (73, 1), (1813081, 1)] : List FactorBlock).map factorBlockValue).prod) = 9264843911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_1813081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9264843911) ^ 4632421955 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 9264843911) ^ 1852968782 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 9264843911) ^ 1323549130 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 9264843911) ^ 126915670 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 9264843911) ^ 5110 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_9548973529 : Nat.Prime 9548973529 := by
  apply lucas_primality 9548973529 (11 : ZMod 9548973529)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (397873897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (397873897, 1)] : List FactorBlock).map factorBlockValue).prod) = 9548973529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_397873897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 9548973529) ^ 4774486764 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 9548973529) ^ 3182991176 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 9548973529) ^ 24 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_11499866111 : Nat.Prime 11499866111 := by
  apply lucas_primality 11499866111 (13 : ZMod 11499866111)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1149986611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1149986611, 1)] : List FactorBlock).map factorBlockValue).prod) = 11499866111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_1149986611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 11499866111) ^ 5749933055 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 11499866111) ^ 2299973222 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 11499866111) ^ 10 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_12016038319 : Nat.Prime 12016038319 := by
  apply lucas_primality 12016038319 (3 : ZMod 12016038319)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (24128591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (24128591, 1)] : List FactorBlock).map factorBlockValue).prod) = 12016038319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_24128591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12016038319) ^ 6008019159 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12016038319) ^ 4005346106 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12016038319) ^ 144771546 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 12016038319) ^ 498 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_13303822387 : Nat.Prime 13303822387 := by
  apply lucas_primality 13303822387 (2 : ZMod 13303822387)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2217303731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2217303731, 1)] : List FactorBlock).map factorBlockValue).prod) = 13303822387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_2217303731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13303822387) ^ 6651911193 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13303822387) ^ 4434607462 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13303822387) ^ 6 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_15697063961 : Nat.Prime 15697063961 := by
  apply lucas_primality 15697063961 (6 : ZMod 15697063961)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (392426599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (392426599, 1)] : List FactorBlock).map factorBlockValue).prod) = 15697063961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_392426599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 15697063961) ^ 7848531980 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 15697063961) ^ 3139412792 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 15697063961) ^ 40 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_16316275697 : Nat.Prime 16316275697 := by
  apply lucas_primality 16316275697 (3 : ZMod 16316275697)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (43, 1), (3387931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (43, 1), (3387931, 1)] : List FactorBlock).map factorBlockValue).prod) = 16316275697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_3387931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16316275697) ^ 8158137848 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16316275697) ^ 2330896528 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16316275697) ^ 379448272 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 16316275697) ^ 4816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_17671923991 : Nat.Prime 17671923991 := by
  apply lucas_primality 17671923991 (3 : ZMod 17671923991)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (4007239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (4007239, 1)] : List FactorBlock).map factorBlockValue).prod) = 17671923991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_4007239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17671923991) ^ 8835961995 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17671923991) ^ 5890641330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17671923991) ^ 3534384798 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17671923991) ^ 2524560570 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 17671923991) ^ 4410 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_17849139431 : Nat.Prime 17849139431 := by
  apply lucas_primality 17849139431 (7 : ZMod 17849139431)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (181, 1), (138893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (181, 1), (138893, 1)] : List FactorBlock).map factorBlockValue).prod) = 17849139431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_181
      · exact prime_eightyNineCI_138893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 17849139431) ^ 8924569715 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 17849139431) ^ 3569827886 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 17849139431) ^ 251396330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 17849139431) ^ 98614030 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 17849139431) ^ 128510 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_18049735087 : Nat.Prime 18049735087 := by
  apply lucas_primality 18049735087 (5 : ZMod 18049735087)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (81305113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (81305113, 1)] : List FactorBlock).map factorBlockValue).prod) = 18049735087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_37
      · exact prime_eightyNineCI_81305113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18049735087) ^ 9024867543 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18049735087) ^ 6016578362 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18049735087) ^ 487830678 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 18049735087) ^ 222 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_20911706369 : Nat.Prime 20911706369 := by
  apply lucas_primality 20911706369 (3 : ZMod 20911706369)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7, 1), (811, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7, 1), (811, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 20911706369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_811
      · exact prime_eightyNineCI_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20911706369) ^ 10455853184 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20911706369) ^ 2987386624 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20911706369) ^ 25785088 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20911706369) ^ 1453312 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_22557782993 : Nat.Prime 22557782993 := by
  apply lucas_primality 22557782993 (3 : ZMod 22557782993)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19391, 1), (72707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19391, 1), (72707, 1)] : List FactorBlock).map factorBlockValue).prod) = 22557782993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19391
      · exact prime_eightyNineCI_72707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22557782993) ^ 11278891496 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22557782993) ^ 1163312 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 22557782993) ^ 310256 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_26126524649 : Nat.Prime 26126524649 := by
  apply lucas_primality 26126524649 (3 : ZMod 26126524649)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (466545083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (466545083, 1)] : List FactorBlock).map factorBlockValue).prod) = 26126524649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_466545083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26126524649) ^ 13063262324 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126524649) ^ 3732360664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 26126524649) ^ 56 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_27159184571 : Nat.Prime 27159184571 := by
  apply lucas_primality 27159184571 (2 : ZMod 27159184571)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (433, 1), (896047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (433, 1), (896047, 1)] : List FactorBlock).map factorBlockValue).prod) = 27159184571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_433
      · exact prime_eightyNineCI_896047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27159184571) ^ 13579592285 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27159184571) ^ 5431836914 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27159184571) ^ 3879883510 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27159184571) ^ 62723290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 27159184571) ^ 30310 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_27885156781 : Nat.Prime 27885156781 := by
  apply lucas_primality 27885156781 (6 : ZMod 27885156781)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (17, 1), (491, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (17, 1), (491, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) = 27885156781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_491
      · exact prime_eightyNineCI_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27885156781) ^ 13942578390 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 9295052260 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 5577031356 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 2145012060 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 1640303340 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 56792580 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 27885156781) ^ 6510660 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_28740160901 : Nat.Prime 28740160901 := by
  apply lucas_primality 28740160901 (3 : ZMod 28740160901)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (17, 1), (1536907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (17, 1), (1536907, 1)] : List FactorBlock).map factorBlockValue).prod) = 28740160901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_1536907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28740160901) ^ 14370080450 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28740160901) ^ 5748032180 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28740160901) ^ 2612741900 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28740160901) ^ 1690597700 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28740160901) ^ 18700 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_30364164749 : Nat.Prime 30364164749 := by
  apply lucas_primality 30364164749 (2 : ZMod 30364164749)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (103, 1), (857, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (103, 1), (857, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) = 30364164749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_103
      · exact prime_eightyNineCI_857
      · exact prime_eightyNineCI_3739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30364164749) ^ 15182082374 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30364164749) ^ 1320181076 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30364164749) ^ 294797716 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30364164749) ^ 35430764 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30364164749) ^ 8120932 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_32477418829 : Nat.Prime 32477418829 := by
  apply lucas_primality 32477418829 (2 : ZMod 32477418829)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (409, 1), (245083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (409, 1), (245083, 1)] : List FactorBlock).map factorBlockValue).prod) = 32477418829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_409
      · exact prime_eightyNineCI_245083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32477418829) ^ 16238709414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32477418829) ^ 10825806276 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32477418829) ^ 79406892 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 32477418829) ^ 132516 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_35216596903 : Nat.Prime 35216596903 := by
  apply lucas_primality 35216596903 (5 : ZMod 35216596903)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (30411569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (30411569, 1)] : List FactorBlock).map factorBlockValue).prod) = 35216596903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_193
      · exact prime_eightyNineCI_30411569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35216596903) ^ 17608298451 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 35216596903) ^ 11738865634 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 35216596903) ^ 182469414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 35216596903) ^ 1158 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_40397333479 : Nat.Prime 40397333479 := by
  apply lucas_primality 40397333479 (3 : ZMod 40397333479)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1499, 1), (264211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1499, 1), (264211, 1)] : List FactorBlock).map factorBlockValue).prod) = 40397333479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_1499
      · exact prime_eightyNineCI_264211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40397333479) ^ 20198666739 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40397333479) ^ 13465777826 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40397333479) ^ 2376313734 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40397333479) ^ 26949522 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 40397333479) ^ 152898 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_49948346611 : Nat.Prime 49948346611 := by
  apply lucas_primality 49948346611 (2 : ZMod 49948346611)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (3617, 1), (153437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (3617, 1), (153437, 1)] : List FactorBlock).map factorBlockValue).prod) = 49948346611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_3617
      · exact prime_eightyNineCI_153437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49948346611) ^ 24974173305 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49948346611) ^ 16649448870 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49948346611) ^ 9989669322 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49948346611) ^ 13809330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 49948346611) ^ 325530 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_50657681233 : Nat.Prime 50657681233 := by
  apply lucas_primality 50657681233 (5 : ZMod 50657681233)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (113, 1), (115303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (113, 1), (115303, 1)] : List FactorBlock).map factorBlockValue).prod) = 50657681233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_113
      · exact prime_eightyNineCI_115303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 50657681233) ^ 25328840616 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 50657681233) ^ 16885893744 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 50657681233) ^ 448298064 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 50657681233) ^ 439344 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_50801580157 : Nat.Prime 50801580157 := by
  apply lucas_primality 50801580157 (2 : ZMod 50801580157)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3907, 1), (1083559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3907, 1), (1083559, 1)] : List FactorBlock).map factorBlockValue).prod) = 50801580157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_3907
      · exact prime_eightyNineCI_1083559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50801580157) ^ 25400790078 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50801580157) ^ 16933860052 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50801580157) ^ 13002708 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 50801580157) ^ 46884 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_55007712553 : Nat.Prime 55007712553 := by
  apply lucas_primality 55007712553 (5 : ZMod 55007712553)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (8353, 1), (21107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (8353, 1), (21107, 1)] : List FactorBlock).map factorBlockValue).prod) = 55007712553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_8353
      · exact prime_eightyNineCI_21107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55007712553) ^ 27503856276 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55007712553) ^ 18335904184 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55007712553) ^ 4231362504 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55007712553) ^ 6585384 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55007712553) ^ 2606136 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_66606546089 : Nat.Prime 66606546089 := by
  apply lucas_primality 66606546089 (3 : ZMod 66606546089)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (80833187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (80833187, 1)] : List FactorBlock).map factorBlockValue).prod) = 66606546089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_103
      · exact prime_eightyNineCI_80833187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 66606546089) ^ 33303273044 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66606546089) ^ 646665496 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 66606546089) ^ 824 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_99835703039 : Nat.Prime 99835703039 := by
  apply lucas_primality 99835703039 (14 : ZMod 99835703039)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2936344207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2936344207, 1)] : List FactorBlock).map factorBlockValue).prod) = 99835703039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_2936344207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 99835703039) ^ 49917851519 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 99835703039) ^ 5872688414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 99835703039) ^ 34 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_119701310593 : Nat.Prime 119701310593 := by
  apply lucas_primality 119701310593 (5 : ZMod 119701310593)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (71, 1), (4390453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (71, 1), (4390453, 1)] : List FactorBlock).map factorBlockValue).prod) = 119701310593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_4390453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119701310593) ^ 59850655296 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 119701310593) ^ 39900436864 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 119701310593) ^ 1685933952 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 119701310593) ^ 27264 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_127110815147 : Nat.Prime 127110815147 := by
  apply lucas_primality 127110815147 (5 : ZMod 127110815147)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (911, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (911, 1), (76079, 1)] : List FactorBlock).map factorBlockValue).prod) = 127110815147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_911
      · exact prime_eightyNineCI_76079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 127110815147) ^ 63555407573 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 127110815147) ^ 18158687878 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 127110815147) ^ 970311566 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 127110815147) ^ 139528886 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 127110815147) ^ 1670774 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_154778146409 : Nat.Prime 154778146409 := by
  apply lucas_primality 154778146409 (6 : ZMod 154778146409)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 2), (131, 1), (569, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 2), (131, 1), (569, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 154778146409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_569
      · exact prime_eightyNineCI_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 154778146409) ^ 77389073204 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 154778146409) ^ 8146218232 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 154778146409) ^ 1181512568 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 154778146409) ^ 272017832 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 154778146409) ^ 215268632 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_164560044853 : Nat.Prime 164560044853 := by
  apply lucas_primality 164560044853 (2 : ZMod 164560044853)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (89, 1), (815251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (89, 1), (815251, 1)] : List FactorBlock).map factorBlockValue).prod) = 164560044853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_89
      · exact prime_eightyNineCI_815251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 164560044853) ^ 82280022426 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 164560044853) ^ 54853348284 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 164560044853) ^ 23508577836 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 164560044853) ^ 1848989268 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 164560044853) ^ 201852 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_167510082911 : Nat.Prime 167510082911 := by
  apply lucas_primality 167510082911 (23 : ZMod 167510082911)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (83, 1), (2764649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (83, 1), (2764649, 1)] : List FactorBlock).map factorBlockValue).prod) = 167510082911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_2764649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 167510082911) ^ 83755041455 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (23 : ZMod 167510082911) ^ 33502016582 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (23 : ZMod 167510082911) ^ 2294658670 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (23 : ZMod 167510082911) ^ 2018193770 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (23 : ZMod 167510082911) ^ 60590 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_185351578469 : Nat.Prime 185351578469 := by
  apply lucas_primality 185351578469 (2 : ZMod 185351578469)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (6619699231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (6619699231, 1)] : List FactorBlock).map factorBlockValue).prod) = 185351578469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_6619699231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 185351578469) ^ 92675789234 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 185351578469) ^ 26478796924 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 185351578469) ^ 28 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_186339882329 : Nat.Prime 186339882329 := by
  apply lucas_primality 186339882329 (3 : ZMod 186339882329)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4339, 1), (5368169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4339, 1), (5368169, 1)] : List FactorBlock).map factorBlockValue).prod) = 186339882329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_4339
      · exact prime_eightyNineCI_5368169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 186339882329) ^ 93169941164 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186339882329) ^ 42945352 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 186339882329) ^ 34712 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_192330809581 : Nat.Prime 192330809581 := by
  apply lucas_primality 192330809581 (6 : ZMod 192330809581)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (35225423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (35225423, 1)] : List FactorBlock).map factorBlockValue).prod) = 192330809581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_35225423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 192330809581) ^ 96165404790 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 192330809581) ^ 64110269860 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 192330809581) ^ 38466161916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 192330809581) ^ 27475829940 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 192330809581) ^ 14794677660 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 192330809581) ^ 5460 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_193374195821 : Nat.Prime 193374195821 := by
  apply lucas_primality 193374195821 (2 : ZMod 193374195821)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (853, 1), (871919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (853, 1), (871919, 1)] : List FactorBlock).map factorBlockValue).prod) = 193374195821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_853
      · exact prime_eightyNineCI_871919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 193374195821) ^ 96687097910 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 193374195821) ^ 38674839164 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 193374195821) ^ 14874938140 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 193374195821) ^ 226698940 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 193374195821) ^ 221780 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_247009570459 : Nat.Prime 247009570459 := by
  apply lucas_primality 247009570459 (2 : ZMod 247009570459)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (73, 1), (11509159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (73, 1), (11509159, 1)] : List FactorBlock).map factorBlockValue).prod) = 247009570459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_11509159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 247009570459) ^ 123504785229 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 247009570459) ^ 82336523486 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 247009570459) ^ 35287081494 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 247009570459) ^ 3383692746 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 247009570459) ^ 21462 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_264352843019 : Nat.Prime 264352843019 := by
  apply lucas_primality 264352843019 (2 : ZMod 264352843019)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (12016038319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (12016038319, 1)] : List FactorBlock).map factorBlockValue).prod) = 264352843019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_12016038319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 264352843019) ^ 132176421509 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264352843019) ^ 24032076638 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 264352843019) ^ 22 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_279296732257 : Nat.Prime 279296732257 := by
  apply lucas_primality 279296732257 (10 : ZMod 279296732257)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (647, 1), (937, 1), (4799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (647, 1), (937, 1), (4799, 1)] : List FactorBlock).map factorBlockValue).prod) = 279296732257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_647
      · exact prime_eightyNineCI_937
      · exact prime_eightyNineCI_4799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 279296732257) ^ 139648366128 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 279296732257) ^ 93098910752 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 279296732257) ^ 431679648 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 279296732257) ^ 298075488 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 279296732257) ^ 58198944 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_313518295789 : Nat.Prime 313518295789 := by
  apply lucas_primality 313518295789 (6 : ZMod 313518295789)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (26126524649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (26126524649, 1)] : List FactorBlock).map factorBlockValue).prod) = 313518295789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_26126524649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 313518295789) ^ 156759147894 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 313518295789) ^ 104506098596 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 313518295789) ^ 12 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_356982788621 : Nat.Prime 356982788621 := by
  apply lucas_primality 356982788621 (2 : ZMod 356982788621)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17849139431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17849139431, 1)] : List FactorBlock).map factorBlockValue).prod) = 356982788621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_17849139431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 356982788621) ^ 178491394310 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 356982788621) ^ 71396557724 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 356982788621) ^ 20 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_376484645869 : Nat.Prime 376484645869 := by
  apply lucas_primality 376484645869 (2 : ZMod 376484645869)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (429776993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (429776993, 1)] : List FactorBlock).map factorBlockValue).prod) = 376484645869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_429776993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376484645869) ^ 188242322934 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 376484645869) ^ 125494881956 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 376484645869) ^ 5157323916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 376484645869) ^ 876 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_382474104443 : Nat.Prime 382474104443 := by
  apply lucas_primality 382474104443 (2 : ZMod 382474104443)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (39877, 1), (43997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (39877, 1), (43997, 1)] : List FactorBlock).map factorBlockValue).prod) = 382474104443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_109
      · exact prime_eightyNineCI_39877
      · exact prime_eightyNineCI_43997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 382474104443) ^ 191237052221 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382474104443) ^ 3508936738 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382474104443) ^ 9591346 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 382474104443) ^ 8693186 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_386748391643 : Nat.Prime 386748391643 := by
  apply lucas_primality 386748391643 (2 : ZMod 386748391643)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193374195821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193374195821, 1)] : List FactorBlock).map factorBlockValue).prod) = 386748391643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_193374195821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 386748391643) ^ 193374195821 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 386748391643) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_404078225321 : Nat.Prime 404078225321 := by
  apply lucas_primality 404078225321 (3 : ZMod 404078225321)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (59, 1), (2223631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (59, 1), (2223631, 1)] : List FactorBlock).map factorBlockValue).prod) = 404078225321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_59
      · exact prime_eightyNineCI_2223631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 404078225321) ^ 202039112660 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404078225321) ^ 80815645064 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404078225321) ^ 57725460760 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404078225321) ^ 36734384120 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404078225321) ^ 6848783480 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 404078225321) ^ 181720 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_436642611187 : Nat.Prime 436642611187 := by
  apply lucas_primality 436642611187 (3 : ZMod 436642611187)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71483, 1), (1018057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71483, 1), (1018057, 1)] : List FactorBlock).map factorBlockValue).prod) = 436642611187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_71483
      · exact prime_eightyNineCI_1018057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 436642611187) ^ 218321305593 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 436642611187) ^ 145547537062 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 436642611187) ^ 6108342 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 436642611187) ^ 428898 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_464456079809 : Nat.Prime 464456079809 := by
  apply lucas_primality 464456079809 (3 : ZMod 464456079809)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (19, 1), (5081, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (19, 1), (5081, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) = 464456079809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_5081
      · exact prime_eightyNineCI_10739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 464456079809) ^ 232228039904 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 464456079809) ^ 66350868544 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 464456079809) ^ 24445056832 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 464456079809) ^ 91410368 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 464456079809) ^ 43249472 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_489830526557 : Nat.Prime 489830526557 := by
  apply lucas_primality 489830526557 (3 : ZMod 489830526557)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (110533, 1), (158269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (110533, 1), (158269, 1)] : List FactorBlock).map factorBlockValue).prod) = 489830526557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_110533
      · exact prime_eightyNineCI_158269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 489830526557) ^ 244915263278 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 489830526557) ^ 69975789508 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 489830526557) ^ 4431532 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 489830526557) ^ 3094924 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_718207863559 : Nat.Prime 718207863559 := by
  apply lucas_primality 718207863559 (3 : ZMod 718207863559)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (119701310593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (119701310593, 1)] : List FactorBlock).map factorBlockValue).prod) = 718207863559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_119701310593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 718207863559) ^ 359103931779 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 718207863559) ^ 239402621186 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 718207863559) ^ 6 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1126778876423 : Nat.Prime 1126778876423 := by
  apply lucas_primality 1126778876423 (5 : ZMod 1126778876423)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (9548973529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (9548973529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126778876423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_59
      · exact prime_eightyNineCI_9548973529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1126778876423) ^ 563389438211 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126778876423) ^ 19097947058 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1126778876423) ^ 118 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1139689934561 : Nat.Prime 1139689934561 := by
  apply lucas_primality 1139689934561 (3 : ZMod 1139689934561)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7123062091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7123062091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139689934561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7123062091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1139689934561) ^ 569844967280 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139689934561) ^ 227937986912 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139689934561) ^ 160 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1293597553103 : Nat.Prime 1293597553103 := by
  apply lucas_primality 1293597553103 (5 : ZMod 1293597553103)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2347, 1), (11981971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2347, 1), (11981971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293597553103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_2347
      · exact prime_eightyNineCI_11981971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1293597553103) ^ 646798776551 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293597553103) ^ 56243371874 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293597553103) ^ 551170666 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293597553103) ^ 107962 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1330382238701 : Nat.Prime 1330382238701 := by
  apply lucas_primality 1330382238701 (2 : ZMod 1330382238701)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13303822387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13303822387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1330382238701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_13303822387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1330382238701) ^ 665191119350 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330382238701) ^ 266076447740 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1330382238701) ^ 100 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1474615470487 : Nat.Prime 1474615470487 := by
  apply lucas_primality 1474615470487 (3 : ZMod 1474615470487)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (28319, 1), (8678599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (28319, 1), (8678599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474615470487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_28319
      · exact prime_eightyNineCI_8678599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1474615470487) ^ 737307735243 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474615470487) ^ 491538490162 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474615470487) ^ 52071594 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1474615470487) ^ 169914 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1717669961089 : Nat.Prime 1717669961089 := by
  apply lucas_primality 1717669961089 (21 : ZMod 1717669961089)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (23, 1), (293, 1), (663763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (23, 1), (293, 1), (663763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1717669961089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_293
      · exact prime_eightyNineCI_663763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 1717669961089) ^ 858834980544 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (21 : ZMod 1717669961089) ^ 572556653696 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (21 : ZMod 1717669961089) ^ 74681302656 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (21 : ZMod 1717669961089) ^ 5862354816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (21 : ZMod 1717669961089) ^ 2587776 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2123775459287 : Nat.Prime 2123775459287 := by
  apply lucas_primality 2123775459287 (5 : ZMod 2123775459287)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (41, 1), (153252667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (41, 1), (153252667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2123775459287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_153252667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2123775459287) ^ 1061887729643 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2123775459287) ^ 163367343022 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2123775459287) ^ 51799401446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2123775459287) ^ 13858 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2704466979733 : Nat.Prime 2704466979733 := by
  apply lucas_primality 2704466979733 (2 : ZMod 2704466979733)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (43, 1), (1307, 1), (81839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (43, 1), (1307, 1), (81839, 1)] : List FactorBlock).map factorBlockValue).prod) = 2704466979733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_1307
      · exact prime_eightyNineCI_81839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2704466979733) ^ 1352233489866 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704466979733) ^ 901488993244 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704466979733) ^ 386352425676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704466979733) ^ 62894580924 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704466979733) ^ 2069217276 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2704466979733) ^ 33046188 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3679780451951 : Nat.Prime 3679780451951 := by
  apply lucas_primality 3679780451951 (7 : ZMod 3679780451951)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (233, 1), (315860983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (233, 1), (315860983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3679780451951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_233
      · exact prime_eightyNineCI_315860983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3679780451951) ^ 1839890225975 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3679780451951) ^ 735956090390 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3679780451951) ^ 15793049150 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 3679780451951) ^ 11650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_3836903348207 : Nat.Prime 3836903348207 := by
  apply lucas_primality 3836903348207 (5 : ZMod 3836903348207)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (66083, 1), (29030941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (66083, 1), (29030941, 1)] : List FactorBlock).map factorBlockValue).prod) = 3836903348207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_66083
      · exact prime_eightyNineCI_29030941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3836903348207) ^ 1918451674103 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3836903348207) ^ 58061882 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3836903348207) ^ 132166 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4070822321477 : Nat.Prime 4070822321477 := by
  apply lucas_primality 4070822321477 (2 : ZMod 4070822321477)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (870601, 1), (1168969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (870601, 1), (1168969, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070822321477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_870601
      · exact prime_eightyNineCI_1168969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4070822321477) ^ 2035411160738 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070822321477) ^ 4675876 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4070822321477) ^ 3482404 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_5120150750249 : Nat.Prime 5120150750249 := by
  apply lucas_primality 5120150750249 (3 : ZMod 5120150750249)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (7711070407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (7711070407, 1)] : List FactorBlock).map factorBlockValue).prod) = 5120150750249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_7711070407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5120150750249) ^ 2560075375124 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5120150750249) ^ 61688563256 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5120150750249) ^ 664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6331346006389 : Nat.Prime 6331346006389 := by
  apply lucas_primality 6331346006389 (2 : ZMod 6331346006389)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (113, 1), (11585941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (113, 1), (11585941, 1)] : List FactorBlock).map factorBlockValue).prod) = 6331346006389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_113
      · exact prime_eightyNineCI_11585941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6331346006389) ^ 3165673003194 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6331346006389) ^ 2110448668796 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6331346006389) ^ 487026615876 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6331346006389) ^ 204236967948 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6331346006389) ^ 56029610676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6331346006389) ^ 546468 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6452582698603 : Nat.Prime 6452582698603 := by
  apply lucas_primality 6452582698603 (2 : ZMod 6452582698603)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (307, 1), (367, 1), (3181681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (307, 1), (367, 1), (3181681, 1)] : List FactorBlock).map factorBlockValue).prod) = 6452582698603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_307
      · exact prime_eightyNineCI_367
      · exact prime_eightyNineCI_3181681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6452582698603) ^ 3226291349301 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6452582698603) ^ 2150860899534 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6452582698603) ^ 21018184686 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6452582698603) ^ 17581969206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6452582698603) ^ 2028042 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6857627371799 : Nat.Prime 6857627371799 := by
  apply lucas_primality 6857627371799 (7 : ZMod 6857627371799)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (489830526557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (489830526557, 1)] : List FactorBlock).map factorBlockValue).prod) = 6857627371799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_489830526557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6857627371799) ^ 3428813685899 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 6857627371799) ^ 979661053114 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 6857627371799) ^ 14 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_8018393055319 : Nat.Prime 8018393055319 := by
  apply lucas_primality 8018393055319 (6 : ZMod 8018393055319)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (53, 1), (269, 1), (1644497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (53, 1), (269, 1), (1644497, 1)] : List FactorBlock).map factorBlockValue).prod) = 8018393055319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_53
      · exact prime_eightyNineCI_269
      · exact prime_eightyNineCI_1644497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8018393055319) ^ 4009196527659 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8018393055319) ^ 2672797685106 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8018393055319) ^ 422020687122 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8018393055319) ^ 151290435006 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8018393055319) ^ 29808152622 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8018393055319) ^ 4875894 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_8806337151529 : Nat.Prime 8806337151529 := by
  apply lucas_primality 8806337151529 (13 : ZMod 8806337151529)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (20947, 1), (2502443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (20947, 1), (2502443, 1)] : List FactorBlock).map factorBlockValue).prod) = 8806337151529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_20947
      · exact prime_eightyNineCI_2502443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8806337151529) ^ 4403168575764 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 8806337151529) ^ 2935445717176 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 8806337151529) ^ 1258048164504 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 8806337151529) ^ 420410424 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 8806337151529) ^ 3519096 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_9669511858177 : Nat.Prime 9669511858177 := by
  apply lucas_primality 9669511858177 (5 : ZMod 9669511858177)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 2), (524604593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 2), (524604593, 1)] : List FactorBlock).map factorBlockValue).prod) = 9669511858177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_524604593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9669511858177) ^ 4834755929088 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9669511858177) ^ 3223170619392 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9669511858177) ^ 18432 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_10659642673349 : Nat.Prime 10659642673349 := by
  apply lucas_primality 10659642673349 (2 : ZMod 10659642673349)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7583, 1), (351432239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7583, 1), (351432239, 1)] : List FactorBlock).map factorBlockValue).prod) = 10659642673349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7583
      · exact prime_eightyNineCI_351432239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10659642673349) ^ 5329821336674 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659642673349) ^ 1405728956 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10659642673349) ^ 30332 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_13134898743349 : Nat.Prime 13134898743349 := by
  apply lucas_primality 13134898743349 (2 : ZMod 13134898743349)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (967, 1), (1131928537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (967, 1), (1131928537, 1)] : List FactorBlock).map factorBlockValue).prod) = 13134898743349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_967
      · exact prime_eightyNineCI_1131928537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13134898743349) ^ 6567449371674 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13134898743349) ^ 4378299581116 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13134898743349) ^ 13583142444 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13134898743349) ^ 11604 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_15297927706631 : Nat.Prime 15297927706631 := by
  apply lucas_primality 15297927706631 (11 : ZMod 15297927706631)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (175327, 1), (513257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (175327, 1), (513257, 1)] : List FactorBlock).map factorBlockValue).prod) = 15297927706631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_175327
      · exact prime_eightyNineCI_513257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15297927706631) ^ 7648963853315 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 15297927706631) ^ 3059585541326 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 15297927706631) ^ 899878100390 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 15297927706631) ^ 87253690 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 15297927706631) ^ 29805590 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_17422635059981 : Nat.Prime 17422635059981 := by
  apply lucas_primality 17422635059981 (2 : ZMod 17422635059981)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47777, 1), (18233287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47777, 1), (18233287, 1)] : List FactorBlock).map factorBlockValue).prod) = 17422635059981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_47777
      · exact prime_eightyNineCI_18233287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17422635059981) ^ 8711317529990 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17422635059981) ^ 3484527011996 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17422635059981) ^ 364665740 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17422635059981) ^ 955540 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_22473064758773 : Nat.Prime 22473064758773 := by
  apply lucas_primality 22473064758773 (2 : ZMod 22473064758773)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (463, 1), (36691, 1), (330721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (463, 1), (36691, 1), (330721, 1)] : List FactorBlock).map factorBlockValue).prod) = 22473064758773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_463
      · exact prime_eightyNineCI_36691
      · exact prime_eightyNineCI_330721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22473064758773) ^ 11236532379386 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22473064758773) ^ 48537936844 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22473064758773) ^ 612495292 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22473064758773) ^ 67951732 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_25142652337291 : Nat.Prime 25142652337291 := by
  apply lucas_primality 25142652337291 (2 : ZMod 25142652337291)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (233, 1), (4409, 1), (815819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (233, 1), (4409, 1), (815819, 1)] : List FactorBlock).map factorBlockValue).prod) = 25142652337291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_233
      · exact prime_eightyNineCI_4409
      · exact prime_eightyNineCI_815819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25142652337291) ^ 12571326168645 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25142652337291) ^ 8380884112430 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25142652337291) ^ 5028530467458 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25142652337291) ^ 107908379130 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25142652337291) ^ 5702574810 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 25142652337291) ^ 30818910 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_38678047432709 : Nat.Prime 38678047432709 := by
  apply lucas_primality 38678047432709 (2 : ZMod 38678047432709)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9669511858177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9669511858177, 1)] : List FactorBlock).map factorBlockValue).prod) = 38678047432709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_9669511858177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 38678047432709) ^ 19339023716354 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 38678047432709) ^ 4 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_42507054901513 : Nat.Prime 42507054901513 := by
  apply lucas_primality 42507054901513 (7 : ZMod 42507054901513)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1877, 1), (314531573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1877, 1), (314531573, 1)] : List FactorBlock).map factorBlockValue).prod) = 42507054901513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_1877
      · exact prime_eightyNineCI_314531573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42507054901513) ^ 21253527450756 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 42507054901513) ^ 14169018300504 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 42507054901513) ^ 22646273256 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 42507054901513) ^ 135144 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_45859402825637 : Nat.Prime 45859402825637 := by
  apply lucas_primality 45859402825637 (2 : ZMod 45859402825637)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (278687, 1), (41138807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (278687, 1), (41138807, 1)] : List FactorBlock).map factorBlockValue).prod) = 45859402825637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_278687
      · exact prime_eightyNineCI_41138807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45859402825637) ^ 22929701412818 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45859402825637) ^ 164555228 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 45859402825637) ^ 1114748 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_49471443834583 : Nat.Prime 49471443834583 := by
  apply lucas_primality 49471443834583 (5 : ZMod 49471443834583)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (31, 1), (109, 1), (81049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (31, 1), (109, 1), (81049, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471443834583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_109
      · exact prime_eightyNineCI_81049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49471443834583) ^ 24735721917291 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 16490481278194 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 7067349119226 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 4497403984962 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 2910084931446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 2150932340634 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 1595853026922 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 453866457198 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 49471443834583) ^ 610389318 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_57648290776327 : Nat.Prime 57648290776327 := by
  apply lucas_primality 57648290776327 (3 : ZMod 57648290776327)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1997, 1), (1603747031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1997, 1), (1603747031, 1)] : List FactorBlock).map factorBlockValue).prod) = 57648290776327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_1997
      · exact prime_eightyNineCI_1603747031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57648290776327) ^ 28824145388163 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 57648290776327) ^ 19216096925442 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 57648290776327) ^ 28867446558 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 57648290776327) ^ 35946 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_137081843827661 : Nat.Prime 137081843827661 := by
  apply lucas_primality 137081843827661 (10 : ZMod 137081843827661)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (463, 1), (11827, 1), (54421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (463, 1), (11827, 1), (54421, 1)] : List FactorBlock).map factorBlockValue).prod) = 137081843827661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_463
      · exact prime_eightyNineCI_11827
      · exact prime_eightyNineCI_54421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 137081843827661) ^ 68540921913830 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 137081843827661) ^ 27416368765532 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 137081843827661) ^ 5960080166420 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 137081843827661) ^ 296073096820 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 137081843827661) ^ 11590584580 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 137081843827661) ^ 2518914460 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_181004482751887 : Nat.Prime 181004482751887 := by
  apply lucas_primality 181004482751887 (3 : ZMod 181004482751887)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (157, 1), (955965833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (157, 1), (955965833, 1)] : List FactorBlock).map factorBlockValue).prod) = 181004482751887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_67
      · exact prime_eightyNineCI_157
      · exact prime_eightyNineCI_955965833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 181004482751887) ^ 90502241375943 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 181004482751887) ^ 60334827583962 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 181004482751887) ^ 2701559444058 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 181004482751887) ^ 1152894794598 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 181004482751887) ^ 189342 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_186693952027493 : Nat.Prime 186693952027493 := by
  apply lucas_primality 186693952027493 (2 : ZMod 186693952027493)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (1217, 1), (421442459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (1217, 1), (421442459, 1)] : List FactorBlock).map factorBlockValue).prod) = 186693952027493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_1217
      · exact prime_eightyNineCI_421442459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186693952027493) ^ 93346976013746 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186693952027493) ^ 26670564575356 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186693952027493) ^ 14361073232884 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186693952027493) ^ 153405055076 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186693952027493) ^ 442988 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_222925002842257 : Nat.Prime 222925002842257 := by
  apply lucas_primality 222925002842257 (15 : ZMod 222925002842257)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (13, 1), (32477418829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (13, 1), (32477418829, 1)] : List FactorBlock).map factorBlockValue).prod) = 222925002842257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_32477418829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 222925002842257) ^ 111462501421128 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (15 : ZMod 222925002842257) ^ 74308334280752 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (15 : ZMod 222925002842257) ^ 20265909349296 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (15 : ZMod 222925002842257) ^ 17148077141712 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (15 : ZMod 222925002842257) ^ 6864 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_284572123381643 : Nat.Prime 284572123381643 := by
  apply lucas_primality 284572123381643 (2 : ZMod 284572123381643)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7883, 1), (18049735087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7883, 1), (18049735087, 1)] : List FactorBlock).map factorBlockValue).prod) = 284572123381643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7883
      · exact prime_eightyNineCI_18049735087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 284572123381643) ^ 142286061690821 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 284572123381643) ^ 36099470174 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 284572123381643) ^ 15766 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_371552353269991 : Nat.Prime 371552353269991 := by
  apply lucas_primality 371552353269991 (6 : ZMod 371552353269991)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (197, 1), (32761031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (197, 1), (32761031, 1)] : List FactorBlock).map factorBlockValue).prod) = 371552353269991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_101
      · exact prime_eightyNineCI_197
      · exact prime_eightyNineCI_32761031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 371552353269991) ^ 185776176634995 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 123850784423330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 74310470653998 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 19555387014210 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 3678736170990 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 1886052554670 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 371552353269991) ^ 11341290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_505809053485867 : Nat.Prime 505809053485867 := by
  apply lucas_primality 505809053485867 (2 : ZMod 505809053485867)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (67, 1), (73, 1), (509, 1), (868271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (67, 1), (73, 1), (509, 1), (868271, 1)] : List FactorBlock).map factorBlockValue).prod) = 505809053485867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_67
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_509
      · exact prime_eightyNineCI_868271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 505809053485867) ^ 252904526742933 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 168603017828622 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 38908388729682 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 7549388857998 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 6928891143642 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 993730949874 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 505809053485867) ^ 582547446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_528751273286569 : Nat.Prime 528751273286569 := by
  apply lucas_primality 528751273286569 (19 : ZMod 528751273286569)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1615199, 1), (13639993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1615199, 1), (13639993, 1)] : List FactorBlock).map factorBlockValue).prod) = 528751273286569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_1615199
      · exact prime_eightyNineCI_13639993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 528751273286569) ^ 264375636643284 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 528751273286569) ^ 176250424428856 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 528751273286569) ^ 327359832 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 528751273286569) ^ 38764776 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_538502089479803 : Nat.Prime 538502089479803 := by
  apply lucas_primality 538502089479803 (2 : ZMod 538502089479803)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (359, 1), (557, 1), (192357761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (359, 1), (557, 1), (192357761, 1)] : List FactorBlock).map factorBlockValue).prod) = 538502089479803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_359
      · exact prime_eightyNineCI_557
      · exact prime_eightyNineCI_192357761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 538502089479803) ^ 269251044739901 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 538502089479803) ^ 76928869925686 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 538502089479803) ^ 1500005820278 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 538502089479803) ^ 966790106786 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 538502089479803) ^ 2799482 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_563605577697857 : Nat.Prime 563605577697857 := by
  apply lucas_primality 563605577697857 (3 : ZMod 563605577697857)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (8806337151529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (8806337151529, 1)] : List FactorBlock).map factorBlockValue).prod) = 563605577697857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_8806337151529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 563605577697857) ^ 281802788848928 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 563605577697857) ^ 64 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_580732442874271 : Nat.Prime 580732442874271 := by
  apply lucas_primality 580732442874271 (14 : ZMod 580732442874271)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (6452582698603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (6452582698603, 1)] : List FactorBlock).map factorBlockValue).prod) = 580732442874271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_6452582698603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 580732442874271) ^ 290366221437135 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 580732442874271) ^ 193577480958090 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 580732442874271) ^ 116146488574854 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (14 : ZMod 580732442874271) ^ 90 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_608412098422873 : Nat.Prime 608412098422873 := by
  apply lucas_primality 608412098422873 (5 : ZMod 608412098422873)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2179, 1), (2621, 1), (1479589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2179, 1), (2621, 1), (1479589, 1)] : List FactorBlock).map factorBlockValue).prod) = 608412098422873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_2179
      · exact prime_eightyNineCI_2621
      · exact prime_eightyNineCI_1479589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 608412098422873) ^ 304206049211436 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 608412098422873) ^ 202804032807624 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 608412098422873) ^ 279216199368 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 608412098422873) ^ 232129759032 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 608412098422873) ^ 411203448 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_610655067373891 : Nat.Prime 610655067373891 := by
  apply lucas_primality 610655067373891 (13 : ZMod 610655067373891)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (264352843019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (264352843019, 1)] : List FactorBlock).map factorBlockValue).prod) = 610655067373891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_264352843019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 610655067373891) ^ 305327533686945 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 610655067373891) ^ 203551689124630 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 610655067373891) ^ 122131013474778 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 610655067373891) ^ 87236438196270 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 610655067373891) ^ 55514097033990 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 610655067373891) ^ 2310 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_831379549980313 : Nat.Prime 831379549980313 := by
  apply lucas_primality 831379549980313 (5 : ZMod 831379549980313)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (3467, 1), (1110175771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (3467, 1), (1110175771, 1)] : List FactorBlock).map factorBlockValue).prod) = 831379549980313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_3467
      · exact prime_eightyNineCI_1110175771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 831379549980313) ^ 415689774990156 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 831379549980313) ^ 277126516660104 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 831379549980313) ^ 239797966536 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 831379549980313) ^ 748872 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_932899915514569 : Nat.Prime 932899915514569 := by
  apply lucas_primality 932899915514569 (13 : ZMod 932899915514569)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (263, 1), (823, 1), (1667, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (263, 1), (823, 1), (1667, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) = 932899915514569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_263
      · exact prime_eightyNineCI_823
      · exact prime_eightyNineCI_1667
      · exact prime_eightyNineCI_6337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 932899915514569) ^ 466449957757284 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 310966638504856 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 54876465618504 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 3547147967736 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 1133535741816 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 559628023704 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 932899915514569) ^ 147214757064 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1237697517846689 : Nat.Prime 1237697517846689 := by
  apply lucas_primality 1237697517846689 (3 : ZMod 1237697517846689)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (38678047432709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (38678047432709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1237697517846689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_38678047432709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1237697517846689) ^ 618848758923344 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1237697517846689) ^ 32 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1337550017053543 : Nat.Prime 1337550017053543 := by
  apply lucas_primality 1337550017053543 (3 : ZMod 1337550017053543)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (222925002842257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (222925002842257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1337550017053543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_222925002842257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1337550017053543) ^ 668775008526771 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1337550017053543) ^ 445850005684514 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1337550017053543) ^ 6 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1445943026429959 : Nat.Prime 1445943026429959 := by
  apply lucas_primality 1445943026429959 (7 : ZMod 1445943026429959)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (179, 1), (192330809581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (179, 1), (192330809581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1445943026429959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_179
      · exact prime_eightyNineCI_192330809581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1445943026429959) ^ 722971513214979 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445943026429959) ^ 481981008809986 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445943026429959) ^ 206563289489994 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445943026429959) ^ 8077894002402 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445943026429959) ^ 7518 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1900056751900777 : Nat.Prime 1900056751900777 := by
  apply lucas_primality 1900056751900777 (11 : ZMod 1900056751900777)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (41, 1), (821, 1), (111997679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (41, 1), (821, 1), (111997679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1900056751900777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_821
      · exact prime_eightyNineCI_111997679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1900056751900777) ^ 950028375950388 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1900056751900777) ^ 633352250633592 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1900056751900777) ^ 271436678842968 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1900056751900777) ^ 46342847607336 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1900056751900777) ^ 2314320038856 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1900056751900777) ^ 16965144 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2031202552909037 : Nat.Prime 2031202552909037 := by
  apply lucas_primality 2031202552909037 (2 : ZMod 2031202552909037)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (101, 1), (386748391643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (101, 1), (386748391643, 1)] : List FactorBlock).map factorBlockValue).prod) = 2031202552909037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_101
      · exact prime_eightyNineCI_386748391643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2031202552909037) ^ 1015601276454518 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031202552909037) ^ 156246350223772 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031202552909037) ^ 20110916365436 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031202552909037) ^ 5252 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2056340128560589 : Nat.Prime 2056340128560589 := by
  apply lucas_primality 2056340128560589 (2 : ZMod 2056340128560589)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (1032847, 1), (1418051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (1032847, 1), (1418051, 1)] : List FactorBlock).map factorBlockValue).prod) = 2056340128560589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_1032847
      · exact prime_eightyNineCI_1418051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2056340128560589) ^ 1028170064280294 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056340128560589) ^ 685446709520196 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056340128560589) ^ 158180009889276 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056340128560589) ^ 1990943604 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056340128560589) ^ 1450117188 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2475395035693379 : Nat.Prime 2475395035693379 := by
  apply lucas_primality 2475395035693379 (2 : ZMod 2475395035693379)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1237697517846689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1237697517846689, 1)] : List FactorBlock).map factorBlockValue).prod) = 2475395035693379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_1237697517846689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2475395035693379) ^ 1237697517846689 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2475395035693379) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2726190006651677 : Nat.Prime 2726190006651677 := by
  apply lucas_primality 2726190006651677 (2 : ZMod 2726190006651677)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (1535861, 1), (14314709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (1535861, 1), (14314709, 1)] : List FactorBlock).map factorBlockValue).prod) = 2726190006651677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_1535861
      · exact prime_eightyNineCI_14314709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2726190006651677) ^ 1363095003325838 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2726190006651677) ^ 87941613117796 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2726190006651677) ^ 1775023916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2726190006651677) ^ 190446764 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4935519693742843 : Nat.Prime 4935519693742843 := by
  apply lucas_primality 4935519693742843 (3 : ZMod 4935519693742843)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (19, 1), (31, 1), (71, 1), (385689503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (19, 1), (31, 1), (71, 1), (385689503, 1)] : List FactorBlock).map factorBlockValue).prod) = 4935519693742843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_385689503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4935519693742843) ^ 2467759846871421 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 1645173231247614 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 290324687867226 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 259764194407518 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 159210312701382 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 69514361883702 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4935519693742843) ^ 12796614 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6059310040492103 : Nat.Prime 6059310040492103 := by
  apply lucas_primality 6059310040492103 (5 : ZMod 6059310040492103)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (185683, 1), (16316275697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (185683, 1), (16316275697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6059310040492103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_185683
      · exact prime_eightyNineCI_16316275697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6059310040492103) ^ 3029655020246051 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6059310040492103) ^ 32632551394 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6059310040492103) ^ 371366 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_11416309580099581 : Nat.Prime 11416309580099581 := by
  apply lucas_primality 11416309580099581 (2 : ZMod 11416309580099581)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (41, 1), (356982788621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (41, 1), (356982788621, 1)] : List FactorBlock).map factorBlockValue).prod) = 11416309580099581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_356982788621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11416309580099581) ^ 5708154790049790 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11416309580099581) ^ 3805436526699860 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11416309580099581) ^ 2283261916019916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11416309580099581) ^ 878177660007660 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11416309580099581) ^ 278446575124380 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11416309580099581) ^ 31980 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_13785521343548389 : Nat.Prime 13785521343548389 := by
  apply lucas_primality 13785521343548389 (2 : ZMod 13785521343548389)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 2), (31799, 1), (9756067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 2), (31799, 1), (9756067, 1)] : List FactorBlock).map factorBlockValue).prod) = 13785521343548389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_31799
      · exact prime_eightyNineCI_9756067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13785521343548389) ^ 6892760671774194 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13785521343548389) ^ 4595173781182796 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13785521343548389) ^ 1969360191935484 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13785521343548389) ^ 599370493197756 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13785521343548389) ^ 433520593212 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13785521343548389) ^ 1413020364 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_13975542550857197 : Nat.Prime 13975542550857197 := by
  apply lucas_primality 13975542550857197 (2 : ZMod 13975542550857197)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (971, 1), (133073, 1), (197369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (971, 1), (133073, 1), (197369, 1)] : List FactorBlock).map factorBlockValue).prod) = 13975542550857197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_137
      · exact prime_eightyNineCI_971
      · exact prime_eightyNineCI_133073
      · exact prime_eightyNineCI_197369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13975542550857197) ^ 6987771275428598 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13975542550857197) ^ 102011259495308 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13975542550857197) ^ 14392937745476 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13975542550857197) ^ 105021623852 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13975542550857197) ^ 70809207884 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_16262204252510831 : Nat.Prime 16262204252510831 := by
  apply lucas_primality 16262204252510831 (19 : ZMod 16262204252510831)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (204623, 1), (7947398021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (204623, 1), (7947398021, 1)] : List FactorBlock).map factorBlockValue).prod) = 16262204252510831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_204623
      · exact prime_eightyNineCI_7947398021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 16262204252510831) ^ 8131102126255415 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 16262204252510831) ^ 3252440850502166 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 16262204252510831) ^ 79473980210 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (19 : ZMod 16262204252510831) ^ 2046230 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_29181835637985587 : Nat.Prime 29181835637985587 := by
  apply lucas_primality 29181835637985587 (2 : ZMod 29181835637985587)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (61339, 1), (705855851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (61339, 1), (705855851, 1)] : List FactorBlock).map factorBlockValue).prod) = 29181835637985587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_337
      · exact prime_eightyNineCI_61339
      · exact prime_eightyNineCI_705855851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29181835637985587) ^ 14590917818992793 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29181835637985587) ^ 86592984088978 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29181835637985587) ^ 475746843574 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29181835637985587) ^ 41342486 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_31902871537823081 : Nat.Prime 31902871537823081 := by
  apply lucas_primality 31902871537823081 (6 : ZMod 31902871537823081)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (5153, 1), (154778146409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (5153, 1), (154778146409, 1)] : List FactorBlock).map factorBlockValue).prod) = 31902871537823081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_5153
      · exact prime_eightyNineCI_154778146409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 31902871537823081) ^ 15951435768911540 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 31902871537823081) ^ 6380574307564616 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 31902871537823081) ^ 6191125856360 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 31902871537823081) ^ 206120 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_37605536158216163 : Nat.Prime 37605536158216163 := by
  apply lucas_primality 37605536158216163 (2 : ZMod 37605536158216163)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (25951, 1), (17671923991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (25951, 1), (17671923991, 1)] : List FactorBlock).map factorBlockValue).prod) = 37605536158216163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_25951
      · exact prime_eightyNineCI_17671923991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37605536158216163) ^ 18802768079108081 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37605536158216163) ^ 917208198980882 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37605536158216163) ^ 1449097767262 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 37605536158216163) ^ 2127982 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_41366739019952083 : Nat.Prime 41366739019952083 := by
  apply lucas_primality 41366739019952083 (2 : ZMod 41366739019952083)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (1201, 1), (3083, 1), (9957307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (1201, 1), (3083, 1), (9957307, 1)] : List FactorBlock).map factorBlockValue).prod) = 41366739019952083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_1201
      · exact prime_eightyNineCI_3083
      · exact prime_eightyNineCI_9957307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41366739019952083) ^ 20683369509976041 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 13788913006650694 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 3760612638177462 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 2433337589408946 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 34443579533682 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 13417690243254 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 41366739019952083) ^ 4154410326 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_53005635860168939 : Nat.Prime 53005635860168939 := by
  apply lucas_primality 53005635860168939 (2 : ZMod 53005635860168939)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (277, 1), (449, 1), (9264843911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (277, 1), (449, 1), (9264843911, 1)] : List FactorBlock).map factorBlockValue).prod) = 53005635860168939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_277
      · exact prime_eightyNineCI_449
      · exact prime_eightyNineCI_9264843911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53005635860168939) ^ 26502817930084469 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53005635860168939) ^ 2304592863485606 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53005635860168939) ^ 191356086137794 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53005635860168939) ^ 118052641113962 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 53005635860168939) ^ 5721158 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_71762202680046511 : Nat.Prime 71762202680046511 := by
  apply lucas_primality 71762202680046511 (12 : ZMod 71762202680046511)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (2393, 1), (91127, 1), (179827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (2393, 1), (91127, 1), (179827, 1)] : List FactorBlock).map factorBlockValue).prod) = 71762202680046511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_61
      · exact prime_eightyNineCI_2393
      · exact prime_eightyNineCI_91127
      · exact prime_eightyNineCI_179827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 71762202680046511) ^ 35881101340023255 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 23920734226682170 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 14352440536009302 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 1176429552131910 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 29988383903070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 787496600130 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (12 : ZMod 71762202680046511) ^ 399062447130 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_80437392556167299 : Nat.Prime 80437392556167299 := by
  apply lucas_primality 80437392556167299 (2 : ZMod 80437392556167299)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (877, 1), (45859402825637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (877, 1), (45859402825637, 1)] : List FactorBlock).map factorBlockValue).prod) = 80437392556167299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_877
      · exact prime_eightyNineCI_45859402825637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 80437392556167299) ^ 40218696278083649 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80437392556167299) ^ 91718805651274 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 80437392556167299) ^ 1754 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_147358630162018811 : Nat.Prime 147358630162018811 := by
  apply lucas_primality 147358630162018811 (2 : ZMod 147358630162018811)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (383, 1), (499, 1), (6761, 1), (112913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (383, 1), (499, 1), (6761, 1), (112913, 1)] : List FactorBlock).map factorBlockValue).prod) = 147358630162018811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_101
      · exact prime_eightyNineCI_383
      · exact prime_eightyNineCI_499
      · exact prime_eightyNineCI_6761
      · exact prime_eightyNineCI_112913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147358630162018811) ^ 73679315081009405 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 29471726032403762 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 1458996338237810 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 384748381624070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 295307876076190 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 21795389759210 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147358630162018811) ^ 1305063457370 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_209383918580902579 : Nat.Prime 209383918580902579 := by
  apply lucas_primality 209383918580902579 (2 : ZMod 209383918580902579)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (3967, 1), (382474104443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (3967, 1), (382474104443, 1)] : List FactorBlock).map factorBlockValue).prod) = 209383918580902579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_3967
      · exact prime_eightyNineCI_382474104443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 209383918580902579) ^ 104691959290451289 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209383918580902579) ^ 69794639526967526 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209383918580902579) ^ 9103648633952286 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209383918580902579) ^ 52781426413134 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 209383918580902579) ^ 547446 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_293190492105954823 : Nat.Prime 293190492105954823 := by
  apply lucas_primality 293190492105954823 (3 : ZMod 293190492105954823)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191627, 1), (453199, 1), (562669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191627, 1), (453199, 1), (562669, 1)] : List FactorBlock).map factorBlockValue).prod) = 293190492105954823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_191627
      · exact prime_eightyNineCI_453199
      · exact prime_eightyNineCI_562669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 293190492105954823) ^ 146595246052977411 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 293190492105954823) ^ 97730164035318274 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 293190492105954823) ^ 1530006168786 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 293190492105954823) ^ 646935434778 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 293190492105954823) ^ 521070988638 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_419266276525715911 : Nat.Prime 419266276525715911 := by
  apply lucas_primality 419266276525715911 (6 : ZMod 419266276525715911)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13975542550857197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13975542550857197, 1)] : List FactorBlock).map factorBlockValue).prod) = 419266276525715911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_13975542550857197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 419266276525715911) ^ 209633138262857955 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 419266276525715911) ^ 139755425508571970 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 419266276525715911) ^ 83853255305143182 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 419266276525715911) ^ 30 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_423639607338809833 : Nat.Prime 423639607338809833 := by
  apply lucas_primality 423639607338809833 (10 : ZMod 423639607338809833)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (79, 1), (433, 1), (27159184571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (79, 1), (433, 1), (27159184571, 1)] : List FactorBlock).map factorBlockValue).prod) = 423639607338809833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_79
      · exact prime_eightyNineCI_433
      · exact prime_eightyNineCI_27159184571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 423639607338809833) ^ 211819803669404916 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 423639607338809833) ^ 141213202446269944 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 423639607338809833) ^ 22296821438884728 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 423639607338809833) ^ 5362526675174808 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 423639607338809833) ^ 978382464985704 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 423639607338809833) ^ 15598392 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_448944956989369021 : Nat.Prime 448944956989369021 := by
  apply lucas_primality 448944956989369021 (2 : ZMod 448944956989369021)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (831379549980313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (831379549980313, 1)] : List FactorBlock).map factorBlockValue).prod) = 448944956989369021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_831379549980313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 448944956989369021) ^ 224472478494684510 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 448944956989369021) ^ 149648318996456340 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 448944956989369021) ^ 89788991397873804 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 448944956989369021) ^ 540 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_482528506651256693 : Nat.Prime 482528506651256693 := by
  apply lucas_primality 482528506651256693 (2 : ZMod 482528506651256693)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (4217, 1), (266239, 1), (9767761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (4217, 1), (266239, 1), (9767761, 1)] : List FactorBlock).map factorBlockValue).prod) = 482528506651256693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_4217
      · exact prime_eightyNineCI_266239
      · exact prime_eightyNineCI_9767761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 482528506651256693) ^ 241264253325628346 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 482528506651256693) ^ 43866227877386972 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 482528506651256693) ^ 114424592518676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 482528506651256693) ^ 1812388518028 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 482528506651256693) ^ 49400113972 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_729398613437735309 : Nat.Prime 729398613437735309 := by
  apply lucas_primality 729398613437735309 (2 : ZMod 729398613437735309)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (139661, 1), (30364164749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (139661, 1), (30364164749, 1)] : List FactorBlock).map factorBlockValue).prod) = 729398613437735309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_139661
      · exact prime_eightyNineCI_30364164749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 729398613437735309) ^ 364699306718867654 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 729398613437735309) ^ 16962758452040356 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 729398613437735309) ^ 5222636336828 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 729398613437735309) ^ 24021692 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1386385838557383919 : Nat.Prime 1386385838557383919 := by
  apply lucas_primality 1386385838557383919 (3 : ZMod 1386385838557383919)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (528751273286569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (528751273286569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1386385838557383919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_528751273286569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1386385838557383919) ^ 693192919278691959 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386385838557383919) ^ 462128612852461306 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386385838557383919) ^ 72967675713546522 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386385838557383919) ^ 60277645154668866 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1386385838557383919) ^ 2622 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1411399837436209729 : Nat.Prime 1411399837436209729 := by
  apply lucas_primality 1411399837436209729 (7 : ZMod 1411399837436209729)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (71534773, 1), (102761783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (71534773, 1), (102761783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1411399837436209729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_71534773
      · exact prime_eightyNineCI_102761783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1411399837436209729) ^ 705699918718104864 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1411399837436209729) ^ 470466612478736576 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1411399837436209729) ^ 19730262336 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1411399837436209729) ^ 13734676416 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1618217967288185533 : Nat.Prime 1618217967288185533 := by
  apply lucas_primality 1618217967288185533 (2 : ZMod 1618217967288185533)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23, 1), (70429, 1), (9249833287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23, 1), (70429, 1), (9249833287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1618217967288185533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_70429
      · exact prime_eightyNineCI_9249833287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1618217967288185533) ^ 809108983644092766 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618217967288185533) ^ 539405989096061844 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618217967288185533) ^ 70357302925573284 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618217967288185533) ^ 22976585884908 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618217967288185533) ^ 174945636 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1787869666210796881 : Nat.Prime 1787869666210796881 := by
  apply lucas_primality 1787869666210796881 (13 : ZMod 1787869666210796881)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1914139, 1), (3891805633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1914139, 1), (3891805633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1787869666210796881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_1914139
      · exact prime_eightyNineCI_3891805633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1787869666210796881) ^ 893934833105398440 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1787869666210796881) ^ 595956555403598960 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1787869666210796881) ^ 357573933242159376 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1787869666210796881) ^ 934033351920 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1787869666210796881) ^ 459393360 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2187791391127837393 : Nat.Prime 2187791391127837393 := by
  apply lucas_primality 2187791391127837393 (7 : ZMod 2187791391127837393)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (29, 1), (59, 1), (131, 1), (982365317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (29, 1), (59, 1), (131, 1), (982365317, 1)] : List FactorBlock).map factorBlockValue).prod) = 2187791391127837393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_29
      · exact prime_eightyNineCI_59
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_982365317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2187791391127837393) ^ 1093895695563918696 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 729263797042612464 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 95121364831645104 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 75441082452684048 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 37081210019115888 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 16700697642197232 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2187791391127837393) ^ 2227064976 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_15363877630194973951 : Nat.Prime 15363877630194973951 := by
  apply lucas_primality 15363877630194973951 (3 : ZMod 15363877630194973951)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (71, 1), (204443, 1), (144006769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (71, 1), (204443, 1), (144006769, 1)] : List FactorBlock).map factorBlockValue).prod) = 15363877630194973951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_71
      · exact prime_eightyNineCI_204443
      · exact prime_eightyNineCI_144006769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15363877630194973951) ^ 7681938815097486975 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 5121292543398324650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 3072775526038994790 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 2194839661456424850 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 216392642678802450 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 75149932402650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15363877630194973951) ^ 106688579550 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_26936697419362141261 : Nat.Prime 26936697419362141261 := by
  apply lucas_primality 26936697419362141261 (6 : ZMod 26936697419362141261)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (448944956989369021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (448944956989369021, 1)] : List FactorBlock).map factorBlockValue).prod) = 26936697419362141261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_448944956989369021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 26936697419362141261) ^ 13468348709681070630 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26936697419362141261) ^ 8978899139787380420 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26936697419362141261) ^ 5387339483872428252 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 26936697419362141261) ^ 60 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_44269806811393002803 : Nat.Prime 44269806811393002803 := by
  apply lucas_primality 44269806811393002803 (2 : ZMod 44269806811393002803)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47657689, 1), (464456079809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47657689, 1), (464456079809, 1)] : List FactorBlock).map factorBlockValue).prod) = 44269806811393002803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_47657689
      · exact prime_eightyNineCI_464456079809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44269806811393002803) ^ 22134903405696501401 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44269806811393002803) ^ 928912159618 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 44269806811393002803) ^ 95315378 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_55019410887798308123 : Nat.Prime 55019410887798308123 := by
  apply lucas_primality 55019410887798308123 (2 : ZMod 55019410887798308123)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1618217967288185533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1618217967288185533, 1)] : List FactorBlock).map factorBlockValue).prod) = 55019410887798308123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_1618217967288185533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55019410887798308123) ^ 27509705443899154061 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 55019410887798308123) ^ 3236435934576371066 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 55019410887798308123) ^ 34 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_90267604162693026647 : Nat.Prime 90267604162693026647 := by
  apply lucas_primality 90267604162693026647 (5 : ZMod 90267604162693026647)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (24197, 1), (22473064758773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (24197, 1), (22473064758773, 1)] : List FactorBlock).map factorBlockValue).prod) = 90267604162693026647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_24197
      · exact prime_eightyNineCI_22473064758773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 90267604162693026647) ^ 45133802081346513323 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 90267604162693026647) ^ 1087561495936060562 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 90267604162693026647) ^ 3730528749956318 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 90267604162693026647) ^ 4016702 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_124193683034671968103 : Nat.Prime 124193683034671968103 := by
  apply lucas_primality 124193683034671968103 (3 : ZMod 124193683034671968103)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (37, 1), (53, 1), (137081843827661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (37, 1), (53, 1), (137081843827661, 1)] : List FactorBlock).map factorBlockValue).prod) = 124193683034671968103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_37
      · exact prime_eightyNineCI_53
      · exact prime_eightyNineCI_137081843827661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 124193683034671968103) ^ 62096841517335984051 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 41397894344890656034 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 17741954719238852586 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 11290334821333815282 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 3356586027964107246 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 2343277038390037134 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 124193683034671968103) ^ 905982 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_235268559070153275983 : Nat.Prime 235268559070153275983 := by
  apply lucas_primality 235268559070153275983 (5 : ZMod 235268559070153275983)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (857, 1), (1433, 1), (3177203, 1), (4306891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (857, 1), (1433, 1), (3177203, 1), (4306891, 1)] : List FactorBlock).map factorBlockValue).prod) = 235268559070153275983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_857
      · exact prime_eightyNineCI_1433
      · exact prime_eightyNineCI_3177203
      · exact prime_eightyNineCI_4306891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 235268559070153275983) ^ 117634279535076637991 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 235268559070153275983) ^ 33609794152879039426 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 235268559070153275983) ^ 274525739871824126 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 235268559070153275983) ^ 164179036336464254 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 235268559070153275983) ^ 74048954086394 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 235268559070153275983) ^ 54626076924202 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_244690548155860923559 : Nat.Prime 244690548155860923559 := by
  apply lucas_primality 244690548155860923559 (3 : ZMod 244690548155860923559)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (80437392556167299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (80437392556167299, 1)] : List FactorBlock).map factorBlockValue).prod) = 244690548155860923559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_80437392556167299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 244690548155860923559) ^ 122345274077930461779 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 244690548155860923559) ^ 81563516051953641186 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 244690548155860923559) ^ 18822349858143147966 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 244690548155860923559) ^ 3042 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_435312616128943296551 : Nat.Prime 435312616128943296551 := by
  apply lucas_primality 435312616128943296551 (13 : ZMod 435312616128943296551)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (131, 1), (577, 1), (2202433, 1), (2273807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (131, 1), (577, 1), (2202433, 1), (2273807, 1)] : List FactorBlock).map factorBlockValue).prod) = 435312616128943296551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_131
      · exact prime_eightyNineCI_577
      · exact prime_eightyNineCI_2202433
      · exact prime_eightyNineCI_2273807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 435312616128943296551) ^ 217656308064471648275 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 87062523225788659310 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 18926635483867099850 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 3322997069686590050 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 754441275786730150 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 197650787165350 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 435312616128943296551) ^ 191446598646650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_452007945847511406539 : Nat.Prime 452007945847511406539 := by
  apply lucas_primality 452007945847511406539 (2 : ZMod 452007945847511406539)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (241, 1), (649483, 1), (35216596903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (241, 1), (649483, 1), (35216596903, 1)] : List FactorBlock).map factorBlockValue).prod) = 452007945847511406539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_241
      · exact prime_eightyNineCI_649483
      · exact prime_eightyNineCI_35216596903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 452007945847511406539) ^ 226003972923755703269 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452007945847511406539) ^ 11024584045061253818 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452007945847511406539) ^ 1875551642520794218 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452007945847511406539) ^ 695950387997086 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 452007945847511406539) ^ 12835083046 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_517148173228596206573 : Nat.Prime 517148173228596206573 := by
  apply lucas_primality 517148173228596206573 (2 : ZMod 517148173228596206573)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (73, 1), (983, 1), (3705773, 1), (44198459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (73, 1), (983, 1), (3705773, 1), (44198459, 1)] : List FactorBlock).map factorBlockValue).prod) = 517148173228596206573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_983
      · exact prime_eightyNineCI_3705773
      · exact prime_eightyNineCI_44198459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 517148173228596206573) ^ 258574086614298103286 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 517148173228596206573) ^ 47013470293508746052 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 517148173228596206573) ^ 7084221551076660364 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 517148173228596206573) ^ 526091732684228084 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 517148173228596206573) ^ 139552037652764 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 517148173228596206573) ^ 11700592847108 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_531757452683225007667 : Nat.Prime 531757452683225007667 := by
  apply lucas_primality 531757452683225007667 (2 : ZMod 531757452683225007667)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (953, 1), (24137, 1), (3218785183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (953, 1), (24137, 1), (3218785183, 1)] : List FactorBlock).map factorBlockValue).prod) = 531757452683225007667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_953
      · exact prime_eightyNineCI_24137
      · exact prime_eightyNineCI_3218785183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 531757452683225007667) ^ 265878726341612503833 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 177252484227741669222 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 75965350383317858238 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 27987234351748684614 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 557982636603593922 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 22030801370643618 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 531757452683225007667) ^ 165204393102 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_644547644923276698283 : Nat.Prime 644547644923276698283 := by
  apply lucas_primality 644547644923276698283 (2 : ZMod 644547644923276698283)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (8377, 1), (610655067373891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (8377, 1), (610655067373891, 1)] : List FactorBlock).map factorBlockValue).prod) = 644547644923276698283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_8377
      · exact prime_eightyNineCI_610655067373891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 644547644923276698283) ^ 322273822461638349141 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 644547644923276698283) ^ 214849214974425566094 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 644547644923276698283) ^ 92078234989039528326 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 644547644923276698283) ^ 76942538489110266 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 644547644923276698283) ^ 1055502 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4246089116636139484267 : Nat.Prime 4246089116636139484267 := by
  apply lucas_primality 4246089116636139484267 (2 : ZMod 4246089116636139484267)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (206980717, 1), (1139689934561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (206980717, 1), (1139689934561, 1)] : List FactorBlock).map factorBlockValue).prod) = 4246089116636139484267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_206980717
      · exact prime_eightyNineCI_1139689934561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4246089116636139484267) ^ 2123044558318069742133 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4246089116636139484267) ^ 1415363038878713161422 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4246089116636139484267) ^ 20514418822098 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4246089116636139484267) ^ 3725652906 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4335965941070712459967 : Nat.Prime 4335965941070712459967 := by
  apply lucas_primality 4335965941070712459967 (3 : ZMod 4335965941070712459967)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (149, 1), (131899, 1), (404078225321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (149, 1), (131899, 1), (404078225321, 1)] : List FactorBlock).map factorBlockValue).prod) = 4335965941070712459967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_149
      · exact prime_eightyNineCI_131899
      · exact prime_eightyNineCI_404078225321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4335965941070712459967) ^ 2167982970535356229983 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 1445321980356904153322 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 619423705867244637138 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 333535841620824035382 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 29100442557521560134 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 32873379942764634 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4335965941070712459967) ^ 10730511246 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_5089464774697045654501 : Nat.Prime 5089464774697045654501 := by
  apply lucas_primality 5089464774697045654501 (2 : ZMod 5089464774697045654501)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (3001, 1), (5380079, 1), (210148457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (3001, 1), (5380079, 1), (210148457, 1)] : List FactorBlock).map factorBlockValue).prod) = 5089464774697045654501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_3001
      · exact prime_eightyNineCI_5380079
      · exact prime_eightyNineCI_210148457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5089464774697045654501) ^ 2544732387348522827250 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5089464774697045654501) ^ 1696488258232348551500 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5089464774697045654501) ^ 1017892954939409130900 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5089464774697045654501) ^ 1695922950582154500 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5089464774697045654501) ^ 945983279185500 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5089464774697045654501) ^ 24218425618500 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6028756649249216490037 : Nat.Prime 6028756649249216490037 := by
  apply lucas_primality 6028756649249216490037 (5 : ZMod 6028756649249216490037)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (13, 1), (19, 1), (173, 1), (1783, 1), (66606546089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (13, 1), (19, 1), (173, 1), (1783, 1), (66606546089, 1)] : List FactorBlock).map factorBlockValue).prod) = 6028756649249216490037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_19
      · exact prime_eightyNineCI_173
      · exact prime_eightyNineCI_1783
      · exact prime_eightyNineCI_66606546089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6028756649249216490037) ^ 3014378324624608245018 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 2009585549749738830012 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 548068786295383317276 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 463750511480708960772 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 317302981539432446844 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 34848304330920326532 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 3381243213263722092 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 6028756649249216490037) ^ 90512975124 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7317450841009587871267 : Nat.Prime 7317450841009587871267 := by
  apply lucas_primality 7317450841009587871267 (5 : ZMod 7317450841009587871267)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (280913, 1), (285119, 1), (1691874157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (280913, 1), (285119, 1), (1691874157, 1)] : List FactorBlock).map factorBlockValue).prod) = 7317450841009587871267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_280913
      · exact prime_eightyNineCI_285119
      · exact prime_eightyNineCI_1691874157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7317450841009587871267) ^ 3658725420504793935633 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7317450841009587871267) ^ 2439150280336529290422 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7317450841009587871267) ^ 26048815259562882 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7317450841009587871267) ^ 25664550033528414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7317450841009587871267) ^ 4325056216938 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_10853981482433099182871 : Nat.Prime 10853981482433099182871 := by
  apply lucas_primality 10853981482433099182871 (29 : ZMod 10853981482433099182871)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (41, 1), (257, 1), (6059310040492103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (41, 1), (257, 1), (6059310040492103, 1)] : List FactorBlock).map factorBlockValue).prod) = 10853981482433099182871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_17
      · exact prime_eightyNineCI_41
      · exact prime_eightyNineCI_257
      · exact prime_eightyNineCI_6059310040492103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 10853981482433099182871) ^ 5426990741216549591435 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 10853981482433099182871) ^ 2170796296486619836574 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 10853981482433099182871) ^ 638469498966652893110 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 10853981482433099182871) ^ 264731255669099980070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 10853981482433099182871) ^ 42233390982229957910 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 10853981482433099182871) ^ 1791290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_13910252299264957259077 : Nat.Prime 13910252299264957259077 := by
  apply lucas_primality 13910252299264957259077 (2 : ZMod 13910252299264957259077)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (317, 1), (1549, 1), (17971, 1), (35569, 1), (3693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (317, 1), (1549, 1), (17971, 1), (35569, 1), (3693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 13910252299264957259077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_317
      · exact prime_eightyNineCI_1549
      · exact prime_eightyNineCI_17971
      · exact prime_eightyNineCI_35569
      · exact prime_eightyNineCI_3693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13910252299264957259077) ^ 6955126149632478629538 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 4636750766421652419692 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 43880922079700180628 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 8980149967246583124 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 774038857006563756 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 391077969559587204 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 13910252299264957259077) ^ 3766481387465604 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_15671254180641958675837 : Nat.Prime 15671254180641958675837 := by
  apply lucas_primality 15671254180641958675837 (6 : ZMod 15671254180641958675837)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (435312616128943296551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (435312616128943296551, 1)] : List FactorBlock).map factorBlockValue).prod) = 15671254180641958675837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_435312616128943296551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 15671254180641958675837) ^ 7835627090320979337918 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 15671254180641958675837) ^ 5223751393547319558612 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 15671254180641958675837) ^ 36 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_21707962964866198365743 : Nat.Prime 21707962964866198365743 := by
  apply lucas_primality 21707962964866198365743 (5 : ZMod 21707962964866198365743)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10853981482433099182871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10853981482433099182871, 1)] : List FactorBlock).map factorBlockValue).prod) = 21707962964866198365743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_10853981482433099182871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 21707962964866198365743) ^ 10853981482433099182871 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21707962964866198365743) ^ 2 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_29269803364038351485069 : Nat.Prime 29269803364038351485069 := by
  apply lucas_primality 29269803364038351485069 (2 : ZMod 29269803364038351485069)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7317450841009587871267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7317450841009587871267, 1)] : List FactorBlock).map factorBlockValue).prod) = 29269803364038351485069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_7317450841009587871267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29269803364038351485069) ^ 14634901682019175742534 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 29269803364038351485069) ^ 4 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_36264555446124214686077 : Nat.Prime 36264555446124214686077 := by
  apply lucas_primality 36264555446124214686077 (2 : ZMod 36264555446124214686077)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (124193683034671968103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (124193683034671968103, 1)] : List FactorBlock).map factorBlockValue).prod) = 36264555446124214686077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_124193683034671968103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36264555446124214686077) ^ 18132277723062107343038 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 36264555446124214686077) ^ 496774732138687872412 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 36264555446124214686077) ^ 292 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_38414661394803261726649 : Nat.Prime 38414661394803261726649 := by
  apply lucas_primality 38414661394803261726649 (11 : ZMod 38414661394803261726649)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (2666527189, 1), (2766177329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (2666527189, 1), (2766177329, 1)] : List FactorBlock).map factorBlockValue).prod) = 38414661394803261726649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_2666527189
      · exact prime_eightyNineCI_2766177329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 38414661394803261726649) ^ 19207330697401630863324 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 38414661394803261726649) ^ 12804887131601087242216 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 38414661394803261726649) ^ 5487808770686180246664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 38414661394803261726649) ^ 1239182625638814894408 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 38414661394803261726649) ^ 14406251529432 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (11 : ZMod 38414661394803261726649) ^ 13887273600312 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_70918960621929913532147 : Nat.Prime 70918960621929913532147 := by
  apply lucas_primality 70918960621929913532147 (2 : ZMod 70918960621929913532147)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (73, 1), (107, 1), (587, 1), (691, 1), (5903, 1), (82434491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (73, 1), (107, 1), (587, 1), (691, 1), (5903, 1), (82434491, 1)] : List FactorBlock).map factorBlockValue).prod) = 70918960621929913532147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_23
      · exact prime_eightyNineCI_73
      · exact prime_eightyNineCI_107
      · exact prime_eightyNineCI_587
      · exact prime_eightyNineCI_691
      · exact prime_eightyNineCI_5903
      · exact prime_eightyNineCI_82434491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70918960621929913532147) ^ 35459480310964956766073 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 3083433070518691892702 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 971492611259313884002 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 662794024504017883478 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 120815946545025406358 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 102632359800188008006 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 12014053976271372782 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 70918960621929913532147) ^ 860306890497206 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_101619739402297361145353 : Nat.Prime 101619739402297361145353 := by
  apply lucas_primality 101619739402297361145353 (3 : ZMod 101619739402297361145353)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6177221, 1), (2056340128560589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6177221, 1), (2056340128560589, 1)] : List FactorBlock).map factorBlockValue).prod) = 101619739402297361145353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_6177221
      · exact prime_eightyNineCI_2056340128560589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 101619739402297361145353) ^ 50809869701148680572676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 101619739402297361145353) ^ 16450721028484712 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 101619739402297361145353) ^ 49417768 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_360427465900578186343963 : Nat.Prime 360427465900578186343963 := by
  apply lucas_primality 360427465900578186343963 (5 : ZMod 360427465900578186343963)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (2801, 1), (19460569, 1), (5482793983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (2801, 1), (19460569, 1), (5482793983, 1)] : List FactorBlock).map factorBlockValue).prod) = 360427465900578186343963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_67
      · exact prime_eightyNineCI_2801
      · exact prime_eightyNineCI_19460569
      · exact prime_eightyNineCI_5482793983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 360427465900578186343963) ^ 180213732950289093171981 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 360427465900578186343963) ^ 120142488633526062114654 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 360427465900578186343963) ^ 5379514416426540094686 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 360427465900578186343963) ^ 128678138486461330362 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 360427465900578186343963) ^ 18520910971337898 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 360427465900578186343963) ^ 65737918845414 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_364442202428481551013131 : Nat.Prime 364442202428481551013131 := by
  apply lucas_primality 364442202428481551013131 (2 : ZMod 364442202428481551013131)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (3701280899, 1), (55007712553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (3701280899, 1), (55007712553, 1)] : List FactorBlock).map factorBlockValue).prod) = 364442202428481551013131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_179
      · exact prime_eightyNineCI_3701280899
      · exact prime_eightyNineCI_55007712553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 364442202428481551013131) ^ 182221101214240775506565 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 364442202428481551013131) ^ 72888440485696310202626 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 364442202428481551013131) ^ 2035989957701014251470 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 364442202428481551013131) ^ 98463805469870 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 364442202428481551013131) ^ 6625292809210 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1816736639475658576064629 : Nat.Prime 1816736639475658576064629 := by
  apply lucas_primality 1816736639475658576064629 (6 : ZMod 1816736639475658576064629)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109201, 1), (1386385838557383919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109201, 1), (1386385838557383919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1816736639475658576064629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_109201
      · exact prime_eightyNineCI_1386385838557383919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1816736639475658576064629) ^ 908368319737829288032314 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1816736639475658576064629) ^ 605578879825219525354876 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1816736639475658576064629) ^ 16636630062688607028 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 1816736639475658576064629) ^ 1310412 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_4641863097103899479817857 : Nat.Prime 4641863097103899479817857 := by
  apply lucas_primality 4641863097103899479817857 (3 : ZMod 4641863097103899479817857)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (36264555446124214686077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (36264555446124214686077, 1)] : List FactorBlock).map factorBlockValue).prod) = 4641863097103899479817857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_36264555446124214686077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4641863097103899479817857) ^ 2320931548551949739908928 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4641863097103899479817857) ^ 128 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7202529446584379040900211 : Nat.Prime 7202529446584379040900211 := by
  apply lucas_primality 7202529446584379040900211 (2 : ZMod 7202529446584379040900211)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1249, 1), (206047, 1), (932899915514569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1249, 1), (206047, 1), (932899915514569, 1)] : List FactorBlock).map factorBlockValue).prod) = 7202529446584379040900211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_1249
      · exact prime_eightyNineCI_206047
      · exact prime_eightyNineCI_932899915514569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7202529446584379040900211) ^ 3601264723292189520450105 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7202529446584379040900211) ^ 2400843148861459680300070 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7202529446584379040900211) ^ 1440505889316875808180042 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7202529446584379040900211) ^ 5766636866760911962290 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7202529446584379040900211) ^ 34955759834330900430 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7202529446584379040900211) ^ 7720581090 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_22344819003005137695585301 : Nat.Prime 22344819003005137695585301 := by
  apply lucas_primality 22344819003005137695585301 (2 : ZMod 22344819003005137695585301)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (258067, 1), (1557137, 1), (185351578469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (258067, 1), (1557137, 1), (185351578469, 1)] : List FactorBlock).map factorBlockValue).prod) = 22344819003005137695585301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_258067
      · exact prime_eightyNineCI_1557137
      · exact prime_eightyNineCI_185351578469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22344819003005137695585301) ^ 11172409501502568847792650 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22344819003005137695585301) ^ 7448273001001712565195100 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22344819003005137695585301) ^ 4468963800601027539117060 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22344819003005137695585301) ^ 86585340252744975900 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22344819003005137695585301) ^ 14349937740227826900 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 22344819003005137695585301) ^ 120553702253700 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_72616806545998063083858649 : Nat.Prime 72616806545998063083858649 := by
  apply lucas_primality 72616806545998063083858649 (13 : ZMod 72616806545998063083858649)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (1493, 1), (3307, 1), (29181835637985587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (1493, 1), (3307, 1), (29181835637985587, 1)] : List FactorBlock).map factorBlockValue).prod) = 72616806545998063083858649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_1493
      · exact prime_eightyNineCI_3307
      · exact prime_eightyNineCI_29181835637985587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 72616806545998063083858649) ^ 36308403272999031541929324 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 72616806545998063083858649) ^ 24205602181999354361286216 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 72616806545998063083858649) ^ 10373829506571151869122664 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 72616806545998063083858649) ^ 48638182549228441449336 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 72616806545998063083858649) ^ 21958514226186290621064 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (13 : ZMod 72616806545998063083858649) ^ 2488424904 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_346124186464313136212207837 : Nat.Prime 346124186464313136212207837 := by
  apply lucas_primality 346124186464313136212207837 (2 : ZMod 346124186464313136212207837)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2887, 1), (72269, 1), (31902871537823081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2887, 1), (72269, 1), (31902871537823081, 1)] : List FactorBlock).map factorBlockValue).prod) = 346124186464313136212207837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_13
      · exact prime_eightyNineCI_2887
      · exact prime_eightyNineCI_72269
      · exact prime_eightyNineCI_31902871537823081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 346124186464313136212207837) ^ 173062093232156568106103918 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346124186464313136212207837) ^ 26624937420331779708631372 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346124186464313136212207837) ^ 119890608404680684521028 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346124186464313136212207837) ^ 4789386686744152212044 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 346124186464313136212207837) ^ 10849311356 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_451595505086485808620219667 : Nat.Prime 451595505086485808620219667 := by
  apply lucas_primality 451595505086485808620219667 (2 : ZMod 451595505086485808620219667)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (436621, 1), (517148173228596206573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (436621, 1), (517148173228596206573, 1)] : List FactorBlock).map factorBlockValue).prod) = 451595505086485808620219667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_436621
      · exact prime_eightyNineCI_517148173228596206573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 451595505086485808620219667) ^ 225797752543242904310109833 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451595505086485808620219667) ^ 1034296346457192413146 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 451595505086485808620219667) ^ 873242 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_471846424597090553401395437 : Nat.Prime 471846424597090553401395437 := by
  apply lucas_primality 471846424597090553401395437 (2 : ZMod 471846424597090553401395437)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (7057, 1), (10177, 1), (16262204252510831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (7057, 1), (10177, 1), (16262204252510831, 1)] : List FactorBlock).map factorBlockValue).prod) = 471846424597090553401395437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_101
      · exact prime_eightyNineCI_7057
      · exact prime_eightyNineCI_10177
      · exact prime_eightyNineCI_16262204252510831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 471846424597090553401395437) ^ 235923212298545276700697718 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 471846424597090553401395437) ^ 4671746778189015380211836 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 471846424597090553401395437) ^ 66862182881832301743148 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 471846424597090553401395437) ^ 46363999665627449484268 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 471846424597090553401395437) ^ 29014911956 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_876847939042926611737593187 : Nat.Prime 876847939042926611737593187 := by
  apply lucas_primality 876847939042926611737593187 (2 : ZMod 876847939042926611737593187)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (401, 1), (364442202428481551013131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (401, 1), (364442202428481551013131, 1)] : List FactorBlock).map factorBlockValue).prod) = 876847939042926611737593187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_401
      · exact prime_eightyNineCI_364442202428481551013131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 876847939042926611737593187) ^ 438423969521463305868796593 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 876847939042926611737593187) ^ 292282646347642203912531062 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 876847939042926611737593187) ^ 2186653214570889306078786 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 876847939042926611737593187) ^ 2406 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_1195701735058536288733081619 : Nat.Prime 1195701735058536288733081619 := by
  apply lucas_primality 1195701735058536288733081619 (2 : ZMod 1195701735058536288733081619)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (734203, 1), (15363877630194973951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (734203, 1), (15363877630194973951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1195701735058536288733081619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_53
      · exact prime_eightyNineCI_734203
      · exact prime_eightyNineCI_15363877630194973951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1195701735058536288733081619) ^ 597850867529268144366540809 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195701735058536288733081619) ^ 22560410095444080919492106 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195701735058536288733081619) ^ 1628571028800667238806 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195701735058536288733081619) ^ 77825518 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2192119847607316529343982967 : Nat.Prime 2192119847607316529343982967 := by
  apply lucas_primality 2192119847607316529343982967 (5 : ZMod 2192119847607316529343982967)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3041, 1), (360427465900578186343963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3041, 1), (360427465900578186343963, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192119847607316529343982967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3041
      · exact prime_eightyNineCI_360427465900578186343963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2192119847607316529343982967) ^ 1096059923803658264671991483 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2192119847607316529343982967) ^ 720854931801156372687926 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 2192119847607316529343982967) ^ 6082 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_2447017504305841707174678661 : Nat.Prime 2447017504305841707174678661 := by
  apply lucas_primality 2447017504305841707174678661 (10 : ZMod 2447017504305841707174678661)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (1861, 1), (442434067, 1), (164560044853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (43, 1), (1861, 1), (442434067, 1), (164560044853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2447017504305841707174678661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_7
      · exact prime_eightyNineCI_43
      · exact prime_eightyNineCI_1861
      · exact prime_eightyNineCI_442434067
      · exact prime_eightyNineCI_164560044853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2447017504305841707174678661) ^ 1223508752152920853587339330 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 815672501435280569058226220 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 489403500861168341434935732 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 349573929186548815310668380 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 56907383821066086213364620 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 1314893876574874641147060 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 5530807157094079980 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2447017504305841707174678661) ^ 14870058564287220 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_6189514863832423141677128381 : Nat.Prime 6189514863832423141677128381 := by
  apply lucas_primality 6189514863832423141677128381 (2 : ZMod 6189514863832423141677128381)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6990673, 1), (44269806811393002803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6990673, 1), (44269806811393002803, 1)] : List FactorBlock).map factorBlockValue).prod) = 6189514863832423141677128381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_6990673
      · exact prime_eightyNineCI_44269806811393002803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6189514863832423141677128381) ^ 3094757431916211570838564190 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6189514863832423141677128381) ^ 1237902972766484628335425676 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6189514863832423141677128381) ^ 885396136227860056060 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6189514863832423141677128381) ^ 139813460 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_7515839477510799529179370177 : Nat.Prime 7515839477510799529179370177 := by
  apply lucas_primality 7515839477510799529179370177 (5 : ZMod 7515839477510799529179370177)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (747863, 1), (1981463581, 1), (2935118339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (747863, 1), (1981463581, 1), (2935118339, 1)] : List FactorBlock).map factorBlockValue).prod) = 7515839477510799529179370177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_747863
      · exact prime_eightyNineCI_1981463581
      · exact prime_eightyNineCI_2935118339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7515839477510799529179370177) ^ 3757919738755399764589685088 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7515839477510799529179370177) ^ 2505279825836933176393123392 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7515839477510799529179370177) ^ 10049754403561614265152 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7515839477510799529179370177) ^ 3793074750189314496 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7515839477510799529179370177) ^ 2560659779077752384 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_8768479390429266117375931871 : Nat.Prime 8768479390429266117375931871 := by
  apply lucas_primality 8768479390429266117375931871 (29 : ZMod 8768479390429266117375931871)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (876847939042926611737593187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (876847939042926611737593187, 1)] : List FactorBlock).map factorBlockValue).prod) = 8768479390429266117375931871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_876847939042926611737593187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 8768479390429266117375931871) ^ 4384239695214633058687965935 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 8768479390429266117375931871) ^ 1753695878085853223475186374 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (29 : ZMod 8768479390429266117375931871) ^ 10 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_9565613880468290309864652949 : Nat.Prime 9565613880468290309864652949 := by
  apply lucas_primality 9565613880468290309864652949 (6 : ZMod 9565613880468290309864652949)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (31, 1), (59, 1), (83, 1), (89, 1), (1787869666210796881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (31, 1), (59, 1), (83, 1), (89, 1), (1787869666210796881, 1)] : List FactorBlock).map factorBlockValue).prod) = 9565613880468290309864652949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_3
      · exact prime_eightyNineCI_11
      · exact prime_eightyNineCI_31
      · exact prime_eightyNineCI_59
      · exact prime_eightyNineCI_83
      · exact prime_eightyNineCI_89
      · exact prime_eightyNineCI_1787869666210796881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9565613880468290309864652949) ^ 4782806940234145154932326474 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 3188537960156096769954884316 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 869601261860753664533150268 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 308568189692525493866601708 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 162129048821496445929909372 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 115248360005642051926080156 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 107478807645711127077130932 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (6 : ZMod 9565613880468290309864652949) ^ 5350285908 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem prime_eightyNineCI_105221752685151193408511182481 : Nat.Prime 105221752685151193408511182481 := by
  apply lucas_primality 105221752685151193408511182481 (3 : ZMod 105221752685151193408511182481)
  · rw [← eightyNineCIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (47, 1), (527953457, 1), (53005635860168939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (47, 1), (527953457, 1), (53005635860168939, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyNineCI_2
      · exact prime_eightyNineCI_5
      · exact prime_eightyNineCI_47
      · exact prime_eightyNineCI_527953457
      · exact prime_eightyNineCI_53005635860168939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105221752685151193408511182481) ^ 52610876342575596704255591240 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105221752685151193408511182481) ^ 21044350537030238681702236496 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105221752685151193408511182481) ^ 2238760695428748795925769840 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105221752685151193408511182481) ^ 199301190834235210640 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide
    · change (3 : ZMod 105221752685151193408511182481) ^ 1985104998320 ≠ 1
      rw [← eightyNineCIFastPow_eq_pow]
      decide

private theorem phi_eightyNineCI_105221752685151193408511182400 : Nat.totient 105221752685151193408511182400 = 40559666044601301321512355840 := by
  rw [← show ((([(2, 6), (5, 2), (29, 1), (523, 1), (4335965941070712459967, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_29, prime_eightyNineCI_523, prime_eightyNineCI_4335965941070712459967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182401 : Nat.totient 105221752685151193408511182401 = 57512510784430465962416049216 := by
  rw [← show ((([(3, 2), (7, 1), (23, 1), (72616806545998063083858649, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_7, prime_eightyNineCI_23, prime_eightyNineCI_72616806545998063083858649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182402 : Nat.totient 105221752685151193408511182402 = 51817918928304454282713196800 := by
  rw [← show ((([(2, 1), (107, 1), (173, 1), (4894063121, 1), (580732442874271, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_107, prime_eightyNineCI_173, prime_eightyNineCI_4894063121, prime_eightyNineCI_580732442874271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182403 : Nat.totient 105221752685151193408511182403 = 105221737493217647659462236448 := by
  rw [← show ((([(8179349, 1), (45205829, 1), (284572123381643, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_8179349, prime_eightyNineCI_45205829, prime_eightyNineCI_284572123381643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182404 : Nat.totient 105221752685151193408511182404 = 32343963464798610416583187968 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (1013, 1), (313518295789, 1), (2123775459287, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_13, prime_eightyNineCI_1013, prime_eightyNineCI_313518295789, prime_eightyNineCI_2123775459287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182405 : Nat.totient 105221752685151193408511182405 = 84054155483090705848049095168 := by
  rw [← show ((([(5, 1), (683, 1), (819337889, 1), (37605536158216163, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_683, prime_eightyNineCI_819337889, prime_eightyNineCI_37605536158216163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182406 : Nat.totient 105221752685151193408511182406 = 47827916659352378926494865440 := by
  rw [← show ((([(2, 1), (11, 1), (316663, 1), (28047757, 1), (538502089479803, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_11, prime_eightyNineCI_316663, prime_eightyNineCI_28047757, prime_eightyNineCI_538502089479803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182407 : Nat.totient 105221752685151193408511182407 = 70147835123015360766825483960 := by
  rw [← show ((([(3, 1), (167510082911, 1), (209383918580902579, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_167510082911, prime_eightyNineCI_209383918580902579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182408 : Nat.totient 105221752685151193408511182408 = 45094986871846484115746059584 := by
  rw [← show ((([(2, 3), (7, 1), (903527, 1), (541995287, 1), (3836903348207, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_7, prime_eightyNineCI_903527, prime_eightyNineCI_541995287, prime_eightyNineCI_3836903348207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182409 : Nat.totient 105221752685151193408511182409 = 98674720717270688063704684800 := by
  rw [← show ((([(17, 1), (277, 1), (22344819003005137695585301, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_17, prime_eightyNineCI_277, prime_eightyNineCI_22344819003005137695585301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182410 : Nat.totient 105221752685151193408511182410 = 26498481558353105926721960448 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (19, 1), (317, 1), (3406525163, 1), (6331346006389, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_19, prime_eightyNineCI_317, prime_eightyNineCI_3406525163, prime_eightyNineCI_6331346006389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182411 : Nat.totient 105221752685151193408511182411 = 104770157180064707599890962512 := by
  rw [← show ((([(233, 1), (451595505086485808620219667, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_233, prime_eightyNineCI_451595505086485808620219667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182412 : Nat.totient 105221752685151193408511182412 = 52608170981472982801927601040 := by
  rw [← show ((([(2, 2), (19447, 1), (3640599539, 1), (371552353269991, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_19447, prime_eightyNineCI_3640599539, prime_eightyNineCI_371552353269991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182413 : Nat.totient 105221752685151193408511182413 = 70147835123432796818229056544 := by
  rw [← show ((([(3, 1), (57648290776327, 1), (608412098422873, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_57648290776327, prime_eightyNineCI_608412098422873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182414 : Nat.totient 105221752685151193408511182414 = 52610876342570650524919175016 := by
  rw [← show ((([(2, 1), (10659642673349, 1), (4935519693742843, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_10659642673349, prime_eightyNineCI_4935519693742843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182415 : Nat.totient 105221752685151193408511182415 = 71979855774683012316166262784 := by
  rw [← show ((([(5, 1), (7, 1), (419, 1), (40514543, 1), (92634953, 1), (1911778769, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_7, prime_eightyNineCI_419, prime_eightyNineCI_40514543, prime_eightyNineCI_92634953, prime_eightyNineCI_1911778769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182416 : Nat.totient 105221752685151193408511182416 = 35073917561717064469503727456 := by
  rw [← show ((([(2, 4), (3, 1), (2192119847607316529343982967, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_2192119847607316529343982967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182417 : Nat.totient 105221752685151193408511182417 = 87602445671974448512669344000 := by
  rw [← show ((([(11, 1), (13, 1), (127, 1), (334043, 1), (13037279, 1), (1330382238701, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_11, prime_eightyNineCI_13, prime_eightyNineCI_127, prime_eightyNineCI_334043, prime_eightyNineCI_13037279, prime_eightyNineCI_1330382238701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182418 : Nat.totient 105221752685151193408511182418 = 50163676663316148437547220992 := by
  rw [← show ((([(2, 1), (37, 1), (67, 1), (193, 1), (82211329, 1), (1337550017053543, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_37, prime_eightyNineCI_67, prime_eightyNineCI_193, prime_eightyNineCI_82211329, prime_eightyNineCI_1337550017053543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182419 : Nat.totient 105221752685151193408511182419 = 70147835120918531112542218800 := by
  rw [← show ((([(3, 2), (27885156781, 1), (419266276525715911, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_27885156781, prime_eightyNineCI_419266276525715911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182420 : Nat.totient 105221752685151193408511182420 = 42085974760976301303398983040 := by
  rw [← show ((([(2, 2), (5, 1), (15791, 1), (690467, 1), (482528506651256693, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_15791, prime_eightyNineCI_690467, prime_eightyNineCI_482528506651256693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182421 : Nat.totient 105221752685151193408511182421 = 105221748439062076772346917292 := by
  rw [← show ((([(24780863, 1), (4246089116636139484267, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_24780863, prime_eightyNineCI_4246089116636139484267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182422 : Nat.totient 105221752685151193408511182422 = 29910752032327242796328035392 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (197, 1), (1816736639475658576064629, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_7, prime_eightyNineCI_197, prime_eightyNineCI_1816736639475658576064629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182423 : Nat.totient 105221752685151193408511182423 = 102774735180845351701336503720 := by
  rw [← show ((([(43, 1), (2447017504305841707174678661, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_43, prime_eightyNineCI_2447017504305841707174678661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182424 : Nat.totient 105221752685151193408511182424 = 50322999063476484377086560000 := by
  rw [← show ((([(2, 3), (23, 1), (112361, 1), (5089464774697045654501, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_23, prime_eightyNineCI_112361, prime_eightyNineCI_5089464774697045654501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182425 : Nat.totient 105221752685151193408511182425 = 56102365799412979927161738240 := by
  rw [← show ((([(3, 1), (5, 2), (3529, 1), (209231003, 1), (1900056751900777, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_3529, prime_eightyNineCI_209231003, prime_eightyNineCI_1900056751900777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182426 : Nat.totient 105221752685151193408511182426 = 49506427269019421951063028736 := by
  rw [← show ((([(2, 1), (17, 1), (5693, 1), (50069, 1), (9635579, 1), (1126778876423, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_17, prime_eightyNineCI_5693, prime_eightyNineCI_50069, prime_eightyNineCI_9635579, prime_eightyNineCI_1126778876423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182427 : Nat.totient 105221752685151193408511182427 = 105221752685148675506420587536 := by
  rw [← show ((([(42507054901513, 1), (2475395035693379, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_42507054901513, prime_eightyNineCI_2475395035693379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182428 : Nat.totient 105221752685151193408511182428 = 29631631220130946905068544000 := by
  rw [← show ((([(2, 2), (3, 2), (11, 2), (31, 1), (59, 1), (83, 1), (89, 1), (1787869666210796881, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_11, prime_eightyNineCI_31, prime_eightyNineCI_59, prime_eightyNineCI_83, prime_eightyNineCI_89, prime_eightyNineCI_1787869666210796881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182429 : Nat.totient 105221752685151193408511182429 = 80484789799627359283235266560 := by
  rw [← show ((([(7, 1), (19, 1), (29, 1), (41, 1), (50657681233, 1), (13134898743349, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_7, prime_eightyNineCI_19, prime_eightyNineCI_29, prime_eightyNineCI_41, prime_eightyNineCI_50657681233, prime_eightyNineCI_13134898743349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182430 : Nat.totient 105221752685151193408511182430 = 38126033230349521514881689600 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (101, 1), (113, 1), (70918960621929913532147, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_13, prime_eightyNineCI_101, prime_eightyNineCI_113, prime_eightyNineCI_70918960621929913532147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182431 : Nat.totient 105221752685151193408511182431 = 70113423077126408058645463040 := by
  rw [← show ((([(3, 1), (2081, 1), (99929, 1), (41432249, 1), (4070822321477, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_2081, prime_eightyNineCI_99929, prime_eightyNineCI_41432249, prime_eightyNineCI_4070822321477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182432 : Nat.totient 105221752685151193408511182432 = 52610776278772013940289946112 := by
  rw [← show ((([(2, 5), (525893, 1), (2311939579, 1), (2704466979733, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_525893, prime_eightyNineCI_2311939579, prime_eightyNineCI_2704466979733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182433 : Nat.totient 105221752685151193408511182433 = 102969957817846767806516872800 := by
  rw [← show ((([(47, 2), (7901, 1), (6028756649249216490037, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_47, prime_eightyNineCI_7901, prime_eightyNineCI_6028756649249216490037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182434 : Nat.totient 105221752685151193408511182434 = 35073917381181856143729119312 := by
  rw [← show ((([(2, 1), (3, 1), (194277437, 1), (90267604162693026647, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_194277437, prime_eightyNineCI_90267604162693026647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182435 : Nat.totient 105221752685151193408511182435 = 84177402040374165046235372640 := by
  rw [← show ((([(5, 1), (781252067, 1), (26936697419362141261, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_781252067, prime_eightyNineCI_26936697419362141261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182436 : Nat.totient 105221752685151193408511182436 = 45070088718480362312195704320 := by
  rw [← show ((([(2, 2), (7, 1), (1811, 1), (948469, 1), (2187791391127837393, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_7, prime_eightyNineCI_1811, prime_eightyNineCI_948469, prime_eightyNineCI_2187791391127837393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182437 : Nat.totient 105221752685151193408511182437 = 68521100353261436741268942144 := by
  rw [← show ((([(3, 3), (53, 1), (227, 1), (40397333479, 1), (8018393055319, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_53, prime_eightyNineCI_227, prime_eightyNineCI_40397333479, prime_eightyNineCI_8018393055319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182438 : Nat.totient 105221752685151193408511182438 = 52213035062815602535371020416 := by
  rw [← show ((([(2, 1), (137, 1), (3779, 1), (101619739402297361145353, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_137, prime_eightyNineCI_3779, prime_eightyNineCI_101619739402297361145353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182439 : Nat.totient 105221752685151193408511182439 = 95656138804682903098646529480 := by
  rw [← show ((([(11, 1), (9565613880468290309864652949, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_11, prime_eightyNineCI_9565613880468290309864652949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182440 : Nat.totient 105221752685151193408511182440 = 28059134049373651575602981952 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (876847939042926611737593187, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_876847939042926611737593187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182441 : Nat.totient 105221752685151193408511182441 = 105221388440519900063121611088 := by
  rw [← show ((([(288877, 1), (247009570459, 1), (1474615470487, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_288877, prime_eightyNineCI_247009570459, prime_eightyNineCI_1474615470487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182442 : Nat.totient 105221752685151193408511182442 = 52592675372332186538046960000 := by
  rw [← show ((([(2, 1), (2953, 1), (136651, 1), (2566386451, 1), (50801580157, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_2953, prime_eightyNineCI_136651, prime_eightyNineCI_2566386451, prime_eightyNineCI_50801580157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182443 : Nat.totient 105221752685151193408511182443 = 52028670094726946148493056000 := by
  rw [← show ((([(3, 1), (7, 1), (13, 2), (17, 1), (251, 1), (5371278907, 1), (1293597553103, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_7, prime_eightyNineCI_13, prime_eightyNineCI_17, prime_eightyNineCI_251, prime_eightyNineCI_5371278907, prime_eightyNineCI_1293597553103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182444 : Nat.totient 105221752685151193408511182444 = 52610875438559705009116384448 := by
  rw [← show ((([(2, 2), (58196849, 1), (452007945847511406539, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_58196849, prime_eightyNineCI_452007945847511406539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182445 : Nat.totient 105221752685151193408511182445 = 84121020520033188612864377280 := by
  rw [← show ((([(5, 1), (1493, 1), (340741031, 1), (41366739019952083, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_1493, prime_eightyNineCI_340741031, prime_eightyNineCI_41366739019952083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182446 : Nat.totient 105221752685151193408511182446 = 34642549873323326764438345728 := by
  rw [← show ((([(2, 1), (3, 2), (97, 1), (499, 1), (163063, 1), (7418557, 1), (99835703039, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_97, prime_eightyNineCI_499, prime_eightyNineCI_163063, prime_eightyNineCI_7418557, prime_eightyNineCI_99835703039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182447 : Nat.totient 105221752685151193408511182447 = 98473901691745954912613644800 := by
  rw [← show ((([(23, 1), (61, 1), (211, 1), (1907, 1), (45127, 1), (6773189, 1), (609796679, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_23, prime_eightyNineCI_61, prime_eightyNineCI_211, prime_eightyNineCI_1907, prime_eightyNineCI_45127, prime_eightyNineCI_6773189, prime_eightyNineCI_609796679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182448 : Nat.totient 105221752685151193408511182448 = 49841882850861091614557928384 := by
  rw [← show ((([(2, 4), (19, 1), (346124186464313136212207837, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_19, prime_eightyNineCI_346124186464313136212207837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182449 : Nat.totient 105221752685151193408511182449 = 70147831567575155633377092096 := by
  rw [← show ((([(3, 1), (20997139, 1), (326243153, 1), (5120150750249, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_20997139, prime_eightyNineCI_326243153, prime_eightyNineCI_5120150750249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182450 : Nat.totient 105221752685151193408511182450 = 32770340891762013052924123200 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (11, 1), (1259, 1), (21707962964866198365743, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_7, prime_eightyNineCI_11, prime_eightyNineCI_1259, prime_eightyNineCI_21707962964866198365743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182451 : Nat.totient 105221752685151193408511182451 = 104749906260554102855109786792 := by
  rw [← show ((([(223, 1), (471846424597090553401395437, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_223, prime_eightyNineCI_471846424597090553401395437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182452 : Nat.totient 105221752685151193408511182452 = 35073917561717064469503727480 := by
  rw [← show ((([(2, 2), (3, 1), (8768479390429266117375931871, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_8768479390429266117375931871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182453 : Nat.totient 105221752685151193408511182453 = 105221752040603548485071235180 := by
  rw [← show ((([(163248991, 1), (644547644923276698283, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_163248991, prime_eightyNineCI_644547644923276698283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182454 : Nat.totient 105221752685151193408511182454 = 52500636614583029886039113472 := by
  rw [← show ((([(2, 1), (479, 1), (130657, 1), (16992323, 1), (49471443834583, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_479, prime_eightyNineCI_130657, prime_eightyNineCI_16992323, prime_eightyNineCI_49471443834583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182455 : Nat.totient 105221752685151193408511182455 = 54595914606366185398491187200 := by
  rw [← show ((([(3, 2), (5, 1), (37, 2), (9677, 1), (47965273, 1), (3679780451951, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_37, prime_eightyNineCI_9677, prime_eightyNineCI_47965273, prime_eightyNineCI_3679780451951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182456 : Nat.totient 105221752685151193408511182456 = 48563885847611951611204170240 := by
  rw [← show ((([(2, 3), (13, 1), (6865886449, 1), (147358630162018811, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_13, prime_eightyNineCI_6865886449, prime_eightyNineCI_147358630162018811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182457 : Nat.totient 105221752685151193408511182457 = 90190051545768255567862069248 := by
  rw [← show ((([(7, 1), (4073197, 1), (2148485147, 1), (1717669961089, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_7, prime_eightyNineCI_4073197, prime_eightyNineCI_2148485147, prime_eightyNineCI_1717669961089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182458 : Nat.totient 105221752685151193408511182458 = 32756507342052643615850496000 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (71, 1), (103, 1), (139, 1), (577, 1), (2711, 1), (5203391, 1), (73089353, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_29, prime_eightyNineCI_71, prime_eightyNineCI_103, prime_eightyNineCI_139, prime_eightyNineCI_577, prime_eightyNineCI_2711, prime_eightyNineCI_5203391, prime_eightyNineCI_73089353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182459 : Nat.totient 105221752685151193408511182459 = 101827313405604304446602793600 := by
  rw [← show ((([(31, 1), (692821, 1), (2411957, 1), (2031202552909037, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_31, prime_eightyNineCI_692821, prime_eightyNineCI_2411957, prime_eightyNineCI_2031202552909037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182460 : Nat.totient 105221752685151193408511182460 = 39612889461992236247534456832 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (6990673, 1), (44269806811393002803, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_17, prime_eightyNineCI_6990673, prime_eightyNineCI_44269806811393002803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182461 : Nat.totient 105221752685151193408511182461 = 63770759202893603621561049600 := by
  rw [← show ((([(3, 1), (11, 1), (279296732257, 1), (11416309580099581, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_11, prime_eightyNineCI_279296732257, prime_eightyNineCI_11416309580099581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182462 : Nat.totient 105221752685151193408511182462 = 52610576293570351659424303104 := by
  rw [← show ((([(2, 1), (193327, 1), (2009857, 1), (30468203, 1), (4443969043, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_193327, prime_eightyNineCI_2009857, prime_eightyNineCI_30468203, prime_eightyNineCI_4443969043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182463 : Nat.totient 105221752685151193408511182463 = 105221668737834444451967277120 := by
  rw [← show ((([(1253897, 1), (3337586869, 1), (25142652337291, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_1253897, prime_eightyNineCI_3337586869, prime_eightyNineCI_25142652337291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182464 : Nat.totient 105221752685151193408511182464 = 30063317685610679741775605760 := by
  rw [← show ((([(2, 7), (3, 3), (7, 1), (747863, 1), (1981463581, 1), (2935118339, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_7, prime_eightyNineCI_747863, prime_eightyNineCI_1981463581, prime_eightyNineCI_2935118339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182465 : Nat.totient 105221752685151193408511182465 = 83024287046231253424051617792 := by
  rw [← show ((([(5, 1), (73, 1), (20911706369, 1), (13785521343548389, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_73, prime_eightyNineCI_20911706369, prime_eightyNineCI_13785521343548389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182466 : Nat.totient 105221752685151193408511182466 = 51387339024367075272455942400 := by
  rw [← show ((([(2, 1), (43, 1), (1799801, 1), (3648184339, 1), (186339882329, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_43, prime_eightyNineCI_1799801, prime_eightyNineCI_3648184339, prime_eightyNineCI_186339882329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182467 : Nat.totient 105221752685151193408511182467 = 66455832027737948672135387520 := by
  rw [← show ((([(3, 1), (19, 1), (5657261, 1), (2567095093, 1), (127110815147, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_19, prime_eightyNineCI_5657261, prime_eightyNineCI_2567095093, prime_eightyNineCI_127110815147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182468 : Nat.totient 105221752685151193408511182468 = 52608656646926763504165465120 := by
  rw [← show ((([(2, 2), (24083, 1), (1497511, 1), (729398613437735309, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_24083, prime_eightyNineCI_1497511, prime_eightyNineCI_729398613437735309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182469 : Nat.totient 105221752685151193408511182469 = 97127675603470565246817212736 := by
  rw [← show ((([(13, 1), (1011509, 1), (1166859443, 1), (6857627371799, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_13, prime_eightyNineCI_1011509, prime_eightyNineCI_1166859443, prime_eightyNineCI_6857627371799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182470 : Nat.totient 105221752685151193408511182470 = 25846232757437084949006336000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (23, 1), (41, 1), (79, 1), (3761, 1), (28669231, 1), (436642611187, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_23, prime_eightyNineCI_41, prime_eightyNineCI_79, prime_eightyNineCI_3761, prime_eightyNineCI_28669231, prime_eightyNineCI_436642611187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182471 : Nat.totient 105221752685151193408511182471 = 90160971990394437780383070720 := by
  rw [← show ((([(7, 2), (7919, 1), (9643, 1), (11353, 1), (215389, 1), (11499866111, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_7, prime_eightyNineCI_7919, prime_eightyNineCI_9643, prime_eightyNineCI_11353, prime_eightyNineCI_215389, prime_eightyNineCI_11499866111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182472 : Nat.totient 105221752685151193408511182472 = 47828069402341451549323264720 := by
  rw [← show ((([(2, 3), (11, 1), (1195701735058536288733081619, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_11, prime_eightyNineCI_1195701735058536288733081619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182473 : Nat.totient 105221752685151193408511182473 = 69756399580873884081317452800 := by
  rw [← show ((([(3, 2), (293, 1), (487, 1), (8233, 1), (346273399, 1), (28740160901, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_293, prime_eightyNineCI_487, prime_eightyNineCI_8233, prime_eightyNineCI_346273399, prime_eightyNineCI_28740160901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182474 : Nat.totient 105221752685151193408511182474 = 52610876097885048548179657836 := by
  rw [← show ((([(2, 1), (215009843, 1), (244690548155860923559, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_215009843, prime_eightyNineCI_244690548155860923559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182475 : Nat.totient 105221752685151193408511182475 = 84177401047732736969312825280 := by
  rw [← show ((([(5, 2), (76497913, 1), (55019410887798308123, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_76497913, prime_eightyNineCI_55019410887798308123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182476 : Nat.totient 105221752685151193408511182476 = 35055350109328648871584448512 := by
  rw [← show ((([(2, 2), (3, 1), (1889, 1), (4641863097103899479817857, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_1889, prime_eightyNineCI_4641863097103899479817857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182477 : Nat.totient 105221752685151193408511182477 = 99032237821318770266834054080 := by
  rw [← show ((([(17, 1), (6189514863832423141677128381, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_17, prime_eightyNineCI_6189514863832423141677128381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182478 : Nat.totient 105221752685151193408511182478 = 45095036865064797175076221056 := by
  rw [← show ((([(2, 1), (7, 1), (7515839477510799529179370177, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_7, prime_eightyNineCI_7515839477510799529179370177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182479 : Nat.totient 105221752685151193408511182479 = 70147776583827400862302088256 := by
  rw [← show ((([(3, 1), (1198297, 1), (29269803364038351485069, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_1198297, prime_eightyNineCI_29269803364038351485069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182480 : Nat.totient 105221752685151193408511182480 = 41193196717864681081717999616 := by
  rw [← show ((([(2, 4), (5, 1), (47, 1), (527953457, 1), (53005635860168939, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_47, prime_eightyNineCI_527953457, prime_eightyNineCI_53005635860168939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182481 : Nat.totient 105221752685151193408511182481 = 105221752685151193408511182480 := by
  rw [← show ((([(105221752685151193408511182481, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_105221752685151193408511182481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182482 : Nat.totient 105221752685151193408511182482 = 32356455518204040275928556416 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (1663, 1), (376484645869, 1), (718207863559, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_13, prime_eightyNineCI_1663, prime_eightyNineCI_376484645869, prime_eightyNineCI_718207863559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182483 : Nat.totient 105221752685151193408511182483 = 95571348284280822368618496000 := by
  rw [← show ((([(11, 1), (1129, 1), (1497521, 1), (360435497, 1), (15697063961, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_11, prime_eightyNineCI_1129, prime_eightyNineCI_1497521, prime_eightyNineCI_360435497, prime_eightyNineCI_15697063961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182484 : Nat.totient 105221752685151193408511182484 = 52409850578691029826190903296 := by
  rw [← show ((([(2, 2), (269, 1), (9649, 1), (3717533, 1), (2726190006651677, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_269, prime_eightyNineCI_9649, prime_eightyNineCI_3717533, prime_eightyNineCI_2726190006651677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182485 : Nat.totient 105221752685151193408511182485 = 47382063955733731008074298624 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (67, 1), (39607, 1), (261167, 1), (1445943026429959, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_7, prime_eightyNineCI_67, prime_eightyNineCI_39607, prime_eightyNineCI_261167, prime_eightyNineCI_1445943026429959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182486 : Nat.totient 105221752685151193408511182486 = 49841882850857558171169675240 := by
  rw [← show ((([(2, 1), (19, 1), (15297927706631, 1), (181004482751887, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_19, prime_eightyNineCI_15297927706631, prime_eightyNineCI_181004482751887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182487 : Nat.totient 105221752685151193408511182487 = 99848903824307804402228254080 := by
  rw [← show ((([(29, 1), (59, 1), (4421, 1), (13910252299264957259077, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_29, prime_eightyNineCI_59, prime_eightyNineCI_4421, prime_eightyNineCI_13910252299264957259077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182488 : Nat.totient 105221752685151193408511182488 = 35073913307657443003637707680 := by
  rw [← show ((([(2, 3), (3, 1), (8244811, 1), (531757452683225007667, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_8244811, prime_eightyNineCI_531757452683225007667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182489 : Nat.totient 105221752685151193408511182489 = 105147453082612277446642215936 := by
  rw [← show ((([(2819, 1), (3169, 1), (27803, 1), (423639607338809833, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2819, prime_eightyNineCI_3169, prime_eightyNineCI_27803, prime_eightyNineCI_423639607338809833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182490 : Nat.totient 105221752685151193408511182490 = 39479494644810866241697570560 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (53, 1), (163, 1), (167, 1), (235268559070153275983, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_5, prime_eightyNineCI_31, prime_eightyNineCI_53, prime_eightyNineCI_163, prime_eightyNineCI_167, prime_eightyNineCI_235268559070153275983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182491 : Nat.totient 105221752685151193408511182491 = 69856511605822164999719347200 := by
  rw [← show ((([(3, 4), (241, 1), (483389, 1), (640019, 1), (17422635059981, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_241, prime_eightyNineCI_483389, prime_eightyNineCI_640019, prime_eightyNineCI_17422635059981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182492 : Nat.totient 105221752685151193408511182492 = 43869482103121873438788264960 := by
  rw [← show ((([(2, 2), (7, 1), (37, 1), (6481, 1), (15671254180641958675837, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_7, prime_eightyNineCI_37, prime_eightyNineCI_6481, prime_eightyNineCI_15671254180641958675837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182493 : Nat.totient 105221752685151193408511182493 = 100646888848844927392165602240 := by
  rw [← show ((([(23, 1), (20130293, 1), (4549948517, 1), (49948346611, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_23, prime_eightyNineCI_20130293, prime_eightyNineCI_4549948517, prime_eightyNineCI_49948346611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182494 : Nat.totient 105221752685151193408511182494 = 29947625134689193147702886400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (17, 1), (547, 1), (5167, 1), (20297, 1), (3532541, 1), (462772799, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_11, prime_eightyNineCI_17, prime_eightyNineCI_547, prime_eightyNineCI_5167, prime_eightyNineCI_20297, prime_eightyNineCI_3532541, prime_eightyNineCI_462772799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182495 : Nat.totient 105221752685151193408511182495 = 77702217364051679090253980160 := by
  rw [← show ((([(5, 1), (13, 1), (22557782993, 1), (71762202680046511, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_5, prime_eightyNineCI_13, prime_eightyNineCI_22557782993, prime_eightyNineCI_71762202680046511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182496 : Nat.totient 105221752685151193408511182496 = 52610261707993279852066595328 := by
  rw [← show ((([(2, 5), (85597, 1), (38414661394803261726649, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_85597, prime_eightyNineCI_38414661394803261726649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182497 : Nat.totient 105221752685151193408511182497 = 70147019799963107981588563920 := by
  rw [← show ((([(3, 1), (92143, 1), (1298291, 1), (293190492105954823, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_3, prime_eightyNineCI_92143, prime_eightyNineCI_1298291, prime_eightyNineCI_293190492105954823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182498 : Nat.totient 105221752685151193408511182498 = 52610863052700069158035880496 := by
  rw [← show ((([(2, 1), (4856309, 1), (21418183, 1), (505809053485867, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_4856309, prime_eightyNineCI_21418183, prime_eightyNineCI_505809053485867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182499 : Nat.totient 105221752685151193408511182499 = 90146858553450088075907028360 := by
  rw [← show ((([(7, 1), (2087, 1), (7202529446584379040900211, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_7, prime_eightyNineCI_2087, prime_eightyNineCI_7202529446584379040900211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182500 : Nat.totient 105221752685151193408511182500 = 27872041709722782466598400000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 4), (151, 1), (21943, 1), (1411399837436209729, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_2, prime_eightyNineCI_3, prime_eightyNineCI_5, prime_eightyNineCI_151, prime_eightyNineCI_21943, prime_eightyNineCI_1411399837436209729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyNineCI_105221752685151193408511182501 : Nat.totient 105221752685151193408511182501 = 105221752685150443108981457152 := by
  rw [← show ((([(186693952027493, 1), (563605577697857, 1)] : List FactorBlock).map factorBlockValue).prod) = 105221752685151193408511182501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyNineCI_186693952027493, prime_eightyNineCI_563605577697857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyNineCI : certifiedKill 1 105221752685151193408511182399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyNineCI_105221752685151193408511182400, phi_eightyNineCI_105221752685151193408511182401, phi_eightyNineCI_105221752685151193408511182402,
    phi_eightyNineCI_105221752685151193408511182403, phi_eightyNineCI_105221752685151193408511182404, phi_eightyNineCI_105221752685151193408511182405,
    phi_eightyNineCI_105221752685151193408511182406, phi_eightyNineCI_105221752685151193408511182407, phi_eightyNineCI_105221752685151193408511182408,
    phi_eightyNineCI_105221752685151193408511182409, phi_eightyNineCI_105221752685151193408511182410, phi_eightyNineCI_105221752685151193408511182411,
    phi_eightyNineCI_105221752685151193408511182412, phi_eightyNineCI_105221752685151193408511182413, phi_eightyNineCI_105221752685151193408511182414,
    phi_eightyNineCI_105221752685151193408511182415, phi_eightyNineCI_105221752685151193408511182416, phi_eightyNineCI_105221752685151193408511182417,
    phi_eightyNineCI_105221752685151193408511182418, phi_eightyNineCI_105221752685151193408511182419, phi_eightyNineCI_105221752685151193408511182420,
    phi_eightyNineCI_105221752685151193408511182421, phi_eightyNineCI_105221752685151193408511182422, phi_eightyNineCI_105221752685151193408511182423,
    phi_eightyNineCI_105221752685151193408511182424, phi_eightyNineCI_105221752685151193408511182425, phi_eightyNineCI_105221752685151193408511182426,
    phi_eightyNineCI_105221752685151193408511182427, phi_eightyNineCI_105221752685151193408511182428, phi_eightyNineCI_105221752685151193408511182429,
    phi_eightyNineCI_105221752685151193408511182430, phi_eightyNineCI_105221752685151193408511182431, phi_eightyNineCI_105221752685151193408511182432,
    phi_eightyNineCI_105221752685151193408511182433, phi_eightyNineCI_105221752685151193408511182434, phi_eightyNineCI_105221752685151193408511182435,
    phi_eightyNineCI_105221752685151193408511182436, phi_eightyNineCI_105221752685151193408511182437, phi_eightyNineCI_105221752685151193408511182438,
    phi_eightyNineCI_105221752685151193408511182439, phi_eightyNineCI_105221752685151193408511182440, phi_eightyNineCI_105221752685151193408511182441,
    phi_eightyNineCI_105221752685151193408511182442, phi_eightyNineCI_105221752685151193408511182443, phi_eightyNineCI_105221752685151193408511182444,
    phi_eightyNineCI_105221752685151193408511182445, phi_eightyNineCI_105221752685151193408511182446, phi_eightyNineCI_105221752685151193408511182447,
    phi_eightyNineCI_105221752685151193408511182448, phi_eightyNineCI_105221752685151193408511182449, phi_eightyNineCI_105221752685151193408511182450,
    phi_eightyNineCI_105221752685151193408511182451, phi_eightyNineCI_105221752685151193408511182452, phi_eightyNineCI_105221752685151193408511182453,
    phi_eightyNineCI_105221752685151193408511182454, phi_eightyNineCI_105221752685151193408511182455, phi_eightyNineCI_105221752685151193408511182456,
    phi_eightyNineCI_105221752685151193408511182457, phi_eightyNineCI_105221752685151193408511182458, phi_eightyNineCI_105221752685151193408511182459,
    phi_eightyNineCI_105221752685151193408511182460, phi_eightyNineCI_105221752685151193408511182461, phi_eightyNineCI_105221752685151193408511182462,
    phi_eightyNineCI_105221752685151193408511182463, phi_eightyNineCI_105221752685151193408511182464, phi_eightyNineCI_105221752685151193408511182465,
    phi_eightyNineCI_105221752685151193408511182466, phi_eightyNineCI_105221752685151193408511182467, phi_eightyNineCI_105221752685151193408511182468,
    phi_eightyNineCI_105221752685151193408511182469, phi_eightyNineCI_105221752685151193408511182470, phi_eightyNineCI_105221752685151193408511182471,
    phi_eightyNineCI_105221752685151193408511182472, phi_eightyNineCI_105221752685151193408511182473, phi_eightyNineCI_105221752685151193408511182474,
    phi_eightyNineCI_105221752685151193408511182475, phi_eightyNineCI_105221752685151193408511182476, phi_eightyNineCI_105221752685151193408511182477,
    phi_eightyNineCI_105221752685151193408511182478, phi_eightyNineCI_105221752685151193408511182479, phi_eightyNineCI_105221752685151193408511182480,
    phi_eightyNineCI_105221752685151193408511182481, phi_eightyNineCI_105221752685151193408511182482, phi_eightyNineCI_105221752685151193408511182483,
    phi_eightyNineCI_105221752685151193408511182484, phi_eightyNineCI_105221752685151193408511182485, phi_eightyNineCI_105221752685151193408511182486,
    phi_eightyNineCI_105221752685151193408511182487, phi_eightyNineCI_105221752685151193408511182488, phi_eightyNineCI_105221752685151193408511182489,
    phi_eightyNineCI_105221752685151193408511182490, phi_eightyNineCI_105221752685151193408511182491, phi_eightyNineCI_105221752685151193408511182492,
    phi_eightyNineCI_105221752685151193408511182493, phi_eightyNineCI_105221752685151193408511182494, phi_eightyNineCI_105221752685151193408511182495,
    phi_eightyNineCI_105221752685151193408511182496, phi_eightyNineCI_105221752685151193408511182497, phi_eightyNineCI_105221752685151193408511182498,
    phi_eightyNineCI_105221752685151193408511182499, phi_eightyNineCI_105221752685151193408511182500, phi_eightyNineCI_105221752685151193408511182501]

end TotientTailPeriodKiller
end Erdos249257
