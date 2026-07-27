import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftySevenEYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftySevenEYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftySevenEYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftySevenEYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftySevenEYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftySevenEYFastPow a n * oneHundredFiftySevenEYFastPow a n * a else oneHundredFiftySevenEYFastPow a n * oneHundredFiftySevenEYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftySevenEY_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftySevenEY_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftySevenEY_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftySevenEY_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftySevenEY_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftySevenEY_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftySevenEY_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftySevenEY_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftySevenEY_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftySevenEY_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftySevenEY_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftySevenEY_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftySevenEY_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftySevenEY_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftySevenEY_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftySevenEY_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftySevenEY_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftySevenEY_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftySevenEY_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftySevenEY_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftySevenEY_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftySevenEY_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftySevenEY_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftySevenEY_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftySevenEY_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftySevenEY_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiftySevenEY_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftySevenEY_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftySevenEY_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftySevenEY_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftySevenEY_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftySevenEY_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftySevenEY_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftySevenEY_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftySevenEY_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftySevenEY_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftySevenEY_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftySevenEY_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiftySevenEY_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftySevenEY_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftySevenEY_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftySevenEY_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftySevenEY_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiftySevenEY_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftySevenEY_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftySevenEY_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFiftySevenEY_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFiftySevenEY_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftySevenEY_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFiftySevenEY_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftySevenEY_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiftySevenEY_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiftySevenEY_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFiftySevenEY_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiftySevenEY_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiftySevenEY_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiftySevenEY_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFiftySevenEY_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFiftySevenEY_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftySevenEY_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftySevenEY_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFiftySevenEY_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFiftySevenEY_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiftySevenEY_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFiftySevenEY_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiftySevenEY_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFiftySevenEY_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFiftySevenEY_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftySevenEY_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFiftySevenEY_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFiftySevenEY_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFiftySevenEY_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFiftySevenEY_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFiftySevenEY_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFiftySevenEY_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftySevenEY_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiftySevenEY_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFiftySevenEY_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiftySevenEY_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFiftySevenEY_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFiftySevenEY_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFiftySevenEY_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFiftySevenEY_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFiftySevenEY_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFiftySevenEY_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFiftySevenEY_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFiftySevenEY_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFiftySevenEY_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFiftySevenEY_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFiftySevenEY_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFiftySevenEY_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredFiftySevenEY_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFiftySevenEY_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFiftySevenEY_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFiftySevenEY_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFiftySevenEY_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFiftySevenEY_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredFiftySevenEY_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFiftySevenEY_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFiftySevenEY_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFiftySevenEY_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFiftySevenEY_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFiftySevenEY_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFiftySevenEY_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFiftySevenEY_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFiftySevenEY_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFiftySevenEY_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFiftySevenEY_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiftySevenEY_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredFiftySevenEY_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredFiftySevenEY_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFiftySevenEY_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredFiftySevenEY_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredFiftySevenEY_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2879 : Nat.Prime 2879 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6373 : Nat.Prime 6373 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6553 : Nat.Prime 6553 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6947 : Nat.Prime 6947 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7151 : Nat.Prime 7151 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7687 : Nat.Prime 7687 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8011 : Nat.Prime 8011 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8081 : Nat.Prime 8081 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8233 : Nat.Prime 8233 := by norm_num

private theorem prime_oneHundredFiftySevenEY_9227 : Nat.Prime 9227 := by norm_num

private theorem prime_oneHundredFiftySevenEY_9281 : Nat.Prime 9281 := by norm_num

private theorem prime_oneHundredFiftySevenEY_9697 : Nat.Prime 9697 := by norm_num

private theorem prime_oneHundredFiftySevenEY_9883 : Nat.Prime 9883 := by norm_num

private theorem prime_oneHundredFiftySevenEY_9907 : Nat.Prime 9907 := by norm_num

private theorem prime_oneHundredFiftySevenEY_10313 : Nat.Prime 10313 := by norm_num

private theorem prime_oneHundredFiftySevenEY_11057 : Nat.Prime 11057 := by norm_num

private theorem prime_oneHundredFiftySevenEY_11311 : Nat.Prime 11311 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12143 : Nat.Prime 12143 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12197 : Nat.Prime 12197 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12391 : Nat.Prime 12391 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12527 : Nat.Prime 12527 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12653 : Nat.Prime 12653 := by norm_num

private theorem prime_oneHundredFiftySevenEY_13033 : Nat.Prime 13033 := by norm_num

private theorem prime_oneHundredFiftySevenEY_13109 : Nat.Prime 13109 := by norm_num

private theorem prime_oneHundredFiftySevenEY_13903 : Nat.Prime 13903 := by norm_num

private theorem prime_oneHundredFiftySevenEY_14813 : Nat.Prime 14813 := by norm_num

private theorem prime_oneHundredFiftySevenEY_14897 : Nat.Prime 14897 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15013 : Nat.Prime 15013 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15193 : Nat.Prime 15193 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15581 : Nat.Prime 15581 := by norm_num

private theorem prime_oneHundredFiftySevenEY_16741 : Nat.Prime 16741 := by norm_num

private theorem prime_oneHundredFiftySevenEY_17117 : Nat.Prime 17117 := by norm_num

private theorem prime_oneHundredFiftySevenEY_17167 : Nat.Prime 17167 := by norm_num

private theorem prime_oneHundredFiftySevenEY_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftySevenEY_17569 : Nat.Prime 17569 := by norm_num

private theorem prime_oneHundredFiftySevenEY_18233 : Nat.Prime 18233 := by norm_num

private theorem prime_oneHundredFiftySevenEY_18869 : Nat.Prime 18869 := by norm_num

private theorem prime_oneHundredFiftySevenEY_19181 : Nat.Prime 19181 := by norm_num

private theorem prime_oneHundredFiftySevenEY_19429 : Nat.Prime 19429 := by norm_num

private theorem prime_oneHundredFiftySevenEY_19603 : Nat.Prime 19603 := by norm_num

private theorem prime_oneHundredFiftySevenEY_20177 : Nat.Prime 20177 := by norm_num

private theorem prime_oneHundredFiftySevenEY_20297 : Nat.Prime 20297 := by norm_num

private theorem prime_oneHundredFiftySevenEY_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftySevenEY_22787 : Nat.Prime 22787 := by norm_num

private theorem prime_oneHundredFiftySevenEY_23677 : Nat.Prime 23677 := by norm_num

private theorem prime_oneHundredFiftySevenEY_23743 : Nat.Prime 23743 := by norm_num

private theorem prime_oneHundredFiftySevenEY_23971 : Nat.Prime 23971 := by norm_num

private theorem prime_oneHundredFiftySevenEY_24793 : Nat.Prime 24793 := by norm_num

private theorem prime_oneHundredFiftySevenEY_25229 : Nat.Prime 25229 := by norm_num

private theorem prime_oneHundredFiftySevenEY_25301 : Nat.Prime 25301 := by norm_num

private theorem prime_oneHundredFiftySevenEY_25867 : Nat.Prime 25867 := by norm_num

private theorem prime_oneHundredFiftySevenEY_26029 : Nat.Prime 26029 := by norm_num

private theorem prime_oneHundredFiftySevenEY_27271 : Nat.Prime 27271 := by norm_num

private theorem prime_oneHundredFiftySevenEY_27409 : Nat.Prime 27409 := by norm_num

private theorem prime_oneHundredFiftySevenEY_27551 : Nat.Prime 27551 := by norm_num

private theorem prime_oneHundredFiftySevenEY_29363 : Nat.Prime 29363 := by norm_num

private theorem prime_oneHundredFiftySevenEY_30011 : Nat.Prime 30011 := by norm_num

private theorem prime_oneHundredFiftySevenEY_30493 : Nat.Prime 30493 := by norm_num

private theorem prime_oneHundredFiftySevenEY_32363 : Nat.Prime 32363 := by norm_num

private theorem prime_oneHundredFiftySevenEY_32579 : Nat.Prime 32579 := by norm_num

private theorem prime_oneHundredFiftySevenEY_32833 : Nat.Prime 32833 := by norm_num

private theorem prime_oneHundredFiftySevenEY_33203 : Nat.Prime 33203 := by norm_num

private theorem prime_oneHundredFiftySevenEY_33613 : Nat.Prime 33613 := by norm_num

private theorem prime_oneHundredFiftySevenEY_33961 : Nat.Prime 33961 := by norm_num

private theorem prime_oneHundredFiftySevenEY_34487 : Nat.Prime 34487 := by norm_num

private theorem prime_oneHundredFiftySevenEY_34897 : Nat.Prime 34897 := by norm_num

private theorem prime_oneHundredFiftySevenEY_35999 : Nat.Prime 35999 := by norm_num

private theorem prime_oneHundredFiftySevenEY_36263 : Nat.Prime 36263 := by norm_num

private theorem prime_oneHundredFiftySevenEY_36781 : Nat.Prime 36781 := by norm_num

private theorem prime_oneHundredFiftySevenEY_37397 : Nat.Prime 37397 := by norm_num

private theorem prime_oneHundredFiftySevenEY_41183 : Nat.Prime 41183 := by norm_num

private theorem prime_oneHundredFiftySevenEY_43133 : Nat.Prime 43133 := by norm_num

private theorem prime_oneHundredFiftySevenEY_45697 : Nat.Prime 45697 := by norm_num

private theorem prime_oneHundredFiftySevenEY_49547 : Nat.Prime 49547 := by norm_num

private theorem prime_oneHundredFiftySevenEY_50867 : Nat.Prime 50867 := by norm_num

private theorem prime_oneHundredFiftySevenEY_51131 : Nat.Prime 51131 := by norm_num

private theorem prime_oneHundredFiftySevenEY_51839 : Nat.Prime 51839 := by norm_num

private theorem prime_oneHundredFiftySevenEY_52153 : Nat.Prime 52153 := by norm_num

private theorem prime_oneHundredFiftySevenEY_52517 : Nat.Prime 52517 := by norm_num

private theorem prime_oneHundredFiftySevenEY_54499 : Nat.Prime 54499 := by norm_num

private theorem prime_oneHundredFiftySevenEY_57587 : Nat.Prime 57587 := by norm_num

private theorem prime_oneHundredFiftySevenEY_58991 : Nat.Prime 58991 := by norm_num

private theorem prime_oneHundredFiftySevenEY_61861 : Nat.Prime 61861 := by norm_num

private theorem prime_oneHundredFiftySevenEY_62597 : Nat.Prime 62597 := by norm_num

private theorem prime_oneHundredFiftySevenEY_65183 : Nat.Prime 65183 := by norm_num

private theorem prime_oneHundredFiftySevenEY_67157 : Nat.Prime 67157 := by norm_num

private theorem prime_oneHundredFiftySevenEY_69691 : Nat.Prime 69691 := by norm_num

private theorem prime_oneHundredFiftySevenEY_70117 : Nat.Prime 70117 := by norm_num

private theorem prime_oneHundredFiftySevenEY_71147 : Nat.Prime 71147 := by norm_num

private theorem prime_oneHundredFiftySevenEY_71761 : Nat.Prime 71761 := by norm_num

private theorem prime_oneHundredFiftySevenEY_75133 : Nat.Prime 75133 := by norm_num

private theorem prime_oneHundredFiftySevenEY_77081 : Nat.Prime 77081 := by norm_num

private theorem prime_oneHundredFiftySevenEY_78697 : Nat.Prime 78697 := by norm_num

private theorem prime_oneHundredFiftySevenEY_82261 : Nat.Prime 82261 := by norm_num

private theorem prime_oneHundredFiftySevenEY_82387 : Nat.Prime 82387 := by norm_num

private theorem prime_oneHundredFiftySevenEY_83761 : Nat.Prime 83761 := by norm_num

private theorem prime_oneHundredFiftySevenEY_84143 : Nat.Prime 84143 := by norm_num

private theorem prime_oneHundredFiftySevenEY_90439 : Nat.Prime 90439 := by norm_num

private theorem prime_oneHundredFiftySevenEY_92671 : Nat.Prime 92671 := by norm_num

private theorem prime_oneHundredFiftySevenEY_96293 : Nat.Prime 96293 := by norm_num

private theorem prime_oneHundredFiftySevenEY_96737 : Nat.Prime 96737 := by norm_num

private theorem prime_oneHundredFiftySevenEY_114547 : Nat.Prime 114547 := by norm_num

private theorem prime_oneHundredFiftySevenEY_118529 : Nat.Prime 118529 := by norm_num

private theorem prime_oneHundredFiftySevenEY_118589 : Nat.Prime 118589 := by norm_num

private theorem prime_oneHundredFiftySevenEY_121997 : Nat.Prime 121997 := by norm_num

private theorem prime_oneHundredFiftySevenEY_123553 : Nat.Prime 123553 := by norm_num

private theorem prime_oneHundredFiftySevenEY_131149 : Nat.Prime 131149 := by norm_num

private theorem prime_oneHundredFiftySevenEY_144829 : Nat.Prime 144829 := by norm_num

private theorem prime_oneHundredFiftySevenEY_153313 : Nat.Prime 153313 := by norm_num

private theorem prime_oneHundredFiftySevenEY_153911 : Nat.Prime 153911 := by norm_num

private theorem prime_oneHundredFiftySevenEY_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftySevenEY_172153 : Nat.Prime 172153 := by norm_num

private theorem prime_oneHundredFiftySevenEY_178609 : Nat.Prime 178609 := by norm_num

private theorem prime_oneHundredFiftySevenEY_199247 : Nat.Prime 199247 := by norm_num

private theorem prime_oneHundredFiftySevenEY_200461 : Nat.Prime 200461 := by norm_num

private theorem prime_oneHundredFiftySevenEY_202067 : Nat.Prime 202067 := by norm_num

private theorem prime_oneHundredFiftySevenEY_202361 : Nat.Prime 202361 := by norm_num

private theorem prime_oneHundredFiftySevenEY_208589 : Nat.Prime 208589 := by norm_num

private theorem prime_oneHundredFiftySevenEY_220747 : Nat.Prime 220747 := by norm_num

private theorem prime_oneHundredFiftySevenEY_229639 : Nat.Prime 229639 := by norm_num

private theorem prime_oneHundredFiftySevenEY_234161 : Nat.Prime 234161 := by norm_num

private theorem prime_oneHundredFiftySevenEY_249199 : Nat.Prime 249199 := by norm_num

private theorem prime_oneHundredFiftySevenEY_251033 : Nat.Prime 251033 := by norm_num

private theorem prime_oneHundredFiftySevenEY_261773 : Nat.Prime 261773 := by norm_num

private theorem prime_oneHundredFiftySevenEY_262781 : Nat.Prime 262781 := by norm_num

private theorem prime_oneHundredFiftySevenEY_297247 : Nat.Prime 297247 := by norm_num

private theorem prime_oneHundredFiftySevenEY_301577 : Nat.Prime 301577 := by norm_num

private theorem prime_oneHundredFiftySevenEY_314267 : Nat.Prime 314267 := by norm_num

private theorem prime_oneHundredFiftySevenEY_318629 : Nat.Prime 318629 := by norm_num

private theorem prime_oneHundredFiftySevenEY_323819 : Nat.Prime 323819 := by norm_num

private theorem prime_oneHundredFiftySevenEY_342071 : Nat.Prime 342071 := by norm_num

private theorem prime_oneHundredFiftySevenEY_346369 : Nat.Prime 346369 := by norm_num

private theorem prime_oneHundredFiftySevenEY_347621 : Nat.Prime 347621 := by norm_num

private theorem prime_oneHundredFiftySevenEY_350087 : Nat.Prime 350087 := by norm_num

private theorem prime_oneHundredFiftySevenEY_386047 : Nat.Prime 386047 := by norm_num

private theorem prime_oneHundredFiftySevenEY_388499 : Nat.Prime 388499 := by norm_num

private theorem prime_oneHundredFiftySevenEY_403679 : Nat.Prime 403679 := by norm_num

private theorem prime_oneHundredFiftySevenEY_414019 : Nat.Prime 414019 := by norm_num

private theorem prime_oneHundredFiftySevenEY_415553 : Nat.Prime 415553 := by norm_num

private theorem prime_oneHundredFiftySevenEY_436253 : Nat.Prime 436253 := by norm_num

private theorem prime_oneHundredFiftySevenEY_436439 : Nat.Prime 436439 := by norm_num

private theorem prime_oneHundredFiftySevenEY_464381 : Nat.Prime 464381 := by norm_num

private theorem prime_oneHundredFiftySevenEY_465011 : Nat.Prime 465011 := by norm_num

private theorem prime_oneHundredFiftySevenEY_488207 : Nat.Prime 488207 := by norm_num

private theorem prime_oneHundredFiftySevenEY_493013 : Nat.Prime 493013 := by norm_num

private theorem prime_oneHundredFiftySevenEY_532199 : Nat.Prime 532199 := by norm_num

private theorem prime_oneHundredFiftySevenEY_536561 : Nat.Prime 536561 := by norm_num

private theorem prime_oneHundredFiftySevenEY_541237 : Nat.Prime 541237 := by norm_num

private theorem prime_oneHundredFiftySevenEY_591973 : Nat.Prime 591973 := by norm_num

private theorem prime_oneHundredFiftySevenEY_634169 : Nat.Prime 634169 := by norm_num

private theorem prime_oneHundredFiftySevenEY_663409 : Nat.Prime 663409 := by norm_num

private theorem prime_oneHundredFiftySevenEY_680831 : Nat.Prime 680831 := by norm_num

private theorem prime_oneHundredFiftySevenEY_686041 : Nat.Prime 686041 := by norm_num

private theorem prime_oneHundredFiftySevenEY_703211 : Nat.Prime 703211 := by norm_num

private theorem prime_oneHundredFiftySevenEY_716747 : Nat.Prime 716747 := by norm_num

private theorem prime_oneHundredFiftySevenEY_744203 : Nat.Prime 744203 := by norm_num

private theorem prime_oneHundredFiftySevenEY_767243 : Nat.Prime 767243 := by norm_num

private theorem prime_oneHundredFiftySevenEY_807083 : Nat.Prime 807083 := by norm_num

private theorem prime_oneHundredFiftySevenEY_881743 : Nat.Prime 881743 := by norm_num

private theorem prime_oneHundredFiftySevenEY_943079 : Nat.Prime 943079 := by norm_num

private theorem prime_oneHundredFiftySevenEY_972319 : Nat.Prime 972319 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1035107 : Nat.Prime 1035107 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1043543 : Nat.Prime 1043543 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1055269 : Nat.Prime 1055269 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1060043 : Nat.Prime 1060043 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1102523 : Nat.Prime 1102523 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1167421 : Nat.Prime 1167421 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1210211 : Nat.Prime 1210211 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1360607 : Nat.Prime 1360607 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1463537 : Nat.Prime 1463537 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1535153 : Nat.Prime 1535153 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1581743 : Nat.Prime 1581743 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1705799 : Nat.Prime 1705799 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1781863 : Nat.Prime 1781863 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1843087 : Nat.Prime 1843087 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1885907 : Nat.Prime 1885907 := by norm_num

private theorem prime_oneHundredFiftySevenEY_1917749 : Nat.Prime 1917749 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2100821 : Nat.Prime 2100821 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2237519 : Nat.Prime 2237519 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2328331 : Nat.Prime 2328331 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2365471 : Nat.Prime 2365471 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2380003 : Nat.Prime 2380003 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2505259 : Nat.Prime 2505259 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2699327 : Nat.Prime 2699327 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2748973 : Nat.Prime 2748973 := by norm_num

private theorem prime_oneHundredFiftySevenEY_2857469 : Nat.Prime 2857469 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3005329 : Nat.Prime 3005329 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3108349 : Nat.Prime 3108349 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3374983 : Nat.Prime 3374983 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3735847 : Nat.Prime 3735847 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3736471 : Nat.Prime 3736471 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3874669 : Nat.Prime 3874669 := by norm_num

private theorem prime_oneHundredFiftySevenEY_3976619 : Nat.Prime 3976619 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4010101 : Nat.Prime 4010101 := by norm_num

private theorem prime_oneHundredFiftySevenEY_4698697 : Nat.Prime 4698697 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5122181 : Nat.Prime 5122181 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5159057 : Nat.Prime 5159057 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5190127 : Nat.Prime 5190127 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5219117 : Nat.Prime 5219117 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5387891 : Nat.Prime 5387891 := by norm_num

private theorem prime_oneHundredFiftySevenEY_5446387 : Nat.Prime 5446387 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6276407 : Nat.Prime 6276407 := by norm_num

private theorem prime_oneHundredFiftySevenEY_6293081 : Nat.Prime 6293081 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7033151 : Nat.Prime 7033151 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7038181 : Nat.Prime 7038181 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7492561 : Nat.Prime 7492561 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7540837 : Nat.Prime 7540837 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7664537 : Nat.Prime 7664537 := by norm_num

private theorem prime_oneHundredFiftySevenEY_7703011 : Nat.Prime 7703011 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8042623 : Nat.Prime 8042623 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8170697 : Nat.Prime 8170697 := by norm_num

private theorem prime_oneHundredFiftySevenEY_8217967 : Nat.Prime 8217967 := by norm_num

private theorem prime_oneHundredFiftySevenEY_10411757 : Nat.Prime 10411757 := by norm_num

private theorem prime_oneHundredFiftySevenEY_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftySevenEY_11278247 : Nat.Prime 11278247 := by norm_num

private theorem prime_oneHundredFiftySevenEY_12185273 : Nat.Prime 12185273 := by norm_num

private theorem prime_oneHundredFiftySevenEY_13875593 : Nat.Prime 13875593 := by norm_num

private theorem prime_oneHundredFiftySevenEY_14719843 : Nat.Prime 14719843 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15122951 : Nat.Prime 15122951 := by norm_num

private theorem prime_oneHundredFiftySevenEY_15856213 : Nat.Prime 15856213 := by norm_num

private theorem prime_oneHundredFiftySevenEY_20286829 : Nat.Prime 20286829 := by norm_num

private theorem prime_oneHundredFiftySevenEY_21703967 : Nat.Prime 21703967 := by norm_num

private theorem prime_oneHundredFiftySevenEY_23336771 : Nat.Prime 23336771 := by norm_num

private theorem prime_oneHundredFiftySevenEY_25569347 : Nat.Prime 25569347 := by norm_num

private theorem prime_oneHundredFiftySevenEY_26490377 : Nat.Prime 26490377 := by norm_num

private theorem prime_oneHundredFiftySevenEY_27361549 : Nat.Prime 27361549 := by norm_num

private theorem prime_oneHundredFiftySevenEY_29016137 : Nat.Prime 29016137 := by norm_num

private theorem prime_oneHundredFiftySevenEY_29537423 : Nat.Prime 29537423 := by norm_num

private theorem prime_oneHundredFiftySevenEY_32053051 : Nat.Prime 32053051 := by
  apply lucas_primality 32053051 (29 : ZMod 32053051)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (23743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (23743, 1)] : List FactorBlock).map factorBlockValue).prod) = 32053051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_23743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 32053051) ^ 16026525 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 32053051) ^ 10684350 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 32053051) ^ 6410610 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 32053051) ^ 1350 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_35235593 : Nat.Prime 35235593 := by
  apply lucas_primality 35235593 (3 : ZMod 35235593)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (20297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (20297, 1)] : List FactorBlock).map factorBlockValue).prod) = 35235593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_20297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35235593) ^ 17617796 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35235593) ^ 5033656 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35235593) ^ 1136632 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35235593) ^ 1736 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_39345491 : Nat.Prime 39345491 := by
  apply lucas_primality 39345491 (2 : ZMod 39345491)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (283, 1), (13903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (283, 1), (13903, 1)] : List FactorBlock).map factorBlockValue).prod) = 39345491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_283
      · exact prime_oneHundredFiftySevenEY_13903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39345491) ^ 19672745 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39345491) ^ 7869098 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39345491) ^ 139030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39345491) ^ 2830 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_42482513 : Nat.Prime 42482513 := by
  apply lucas_primality 42482513 (3 : ZMod 42482513)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (71761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (71761, 1)] : List FactorBlock).map factorBlockValue).prod) = 42482513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_71761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42482513) ^ 21241256 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 42482513) ^ 1148176 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 42482513) ^ 592 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_43103129 : Nat.Prime 43103129 := by
  apply lucas_primality 43103129 (3 : ZMod 43103129)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5387891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5387891, 1)] : List FactorBlock).map factorBlockValue).prod) = 43103129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5387891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 43103129) ^ 21551564 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 43103129) ^ 8 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_43729589 : Nat.Prime 43729589 := by
  apply lucas_primality 43729589 (2 : ZMod 43729589)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1223, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1223, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) = 43729589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_1223
      · exact prime_oneHundredFiftySevenEY_1277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43729589) ^ 21864794 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43729589) ^ 6247084 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43729589) ^ 35756 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 43729589) ^ 34244 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_44595791 : Nat.Prime 44595791 := by
  apply lucas_primality 44595791 (7 : ZMod 44595791)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (84143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (84143, 1)] : List FactorBlock).map factorBlockValue).prod) = 44595791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_53
      · exact prime_oneHundredFiftySevenEY_84143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 44595791) ^ 22297895 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 44595791) ^ 8919158 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 44595791) ^ 841430 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 44595791) ^ 530 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_44851813 : Nat.Prime 44851813 := by
  apply lucas_primality 44851813 (2 : ZMod 44851813)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (547, 1), (6833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (547, 1), (6833, 1)] : List FactorBlock).map factorBlockValue).prod) = 44851813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_547
      · exact prime_oneHundredFiftySevenEY_6833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44851813) ^ 22425906 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44851813) ^ 14950604 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44851813) ^ 81996 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44851813) ^ 6564 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_45660169 : Nat.Prime 45660169 := by
  apply lucas_primality 45660169 (17 : ZMod 45660169)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (634169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (634169, 1)] : List FactorBlock).map factorBlockValue).prod) = 45660169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_634169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 45660169) ^ 22830084 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 45660169) ^ 15220056 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 45660169) ^ 72 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_66598997 : Nat.Prime 66598997 := by
  apply lucas_primality 66598997 (2 : ZMod 66598997)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (101, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (101, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) = 66598997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_9697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66598997) ^ 33299498 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 66598997) ^ 3917588 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 66598997) ^ 659396 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 66598997) ^ 6868 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_69284989 : Nat.Prime 69284989 := by
  apply lucas_primality 69284989 (2 : ZMod 69284989)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (307, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (307, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 69284989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_307
      · exact prime_oneHundredFiftySevenEY_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69284989) ^ 34642494 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69284989) ^ 23094996 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69284989) ^ 225684 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 69284989) ^ 11052 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_70471187 : Nat.Prime 70471187 := by
  apply lucas_primality 70471187 (2 : ZMod 70471187)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (35235593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (35235593, 1)] : List FactorBlock).map factorBlockValue).prod) = 70471187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_35235593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 70471187) ^ 35235593 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 70471187) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_70681673 : Nat.Prime 70681673 := by
  apply lucas_primality 70681673 (5 : ZMod 70681673)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (465011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (465011, 1)] : List FactorBlock).map factorBlockValue).prod) = 70681673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_465011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 70681673) ^ 35340836 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 70681673) ^ 3720088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 70681673) ^ 152 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_72181819 : Nat.Prime 72181819 := by
  apply lucas_primality 72181819 (2 : ZMod 72181819)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4010101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4010101, 1)] : List FactorBlock).map factorBlockValue).prod) = 72181819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_4010101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 72181819) ^ 36090909 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72181819) ^ 24060606 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72181819) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_74588599 : Nat.Prime 74588599 := by
  apply lucas_primality 74588599 (3 : ZMod 74588599)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (591973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (591973, 1)] : List FactorBlock).map factorBlockValue).prod) = 74588599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_591973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 74588599) ^ 37294299 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 74588599) ^ 24862866 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 74588599) ^ 10655514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 74588599) ^ 126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_75278293 : Nat.Prime 75278293 := by
  apply lucas_primality 75278293 (2 : ZMod 75278293)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (202361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (202361, 1)] : List FactorBlock).map factorBlockValue).prod) = 75278293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_202361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75278293) ^ 37639146 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 75278293) ^ 25092764 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 75278293) ^ 2428332 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 75278293) ^ 372 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_75680929 : Nat.Prime 75680929 := by
  apply lucas_primality 75680929 (19 : ZMod 75680929)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (262781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (262781, 1)] : List FactorBlock).map factorBlockValue).prod) = 75680929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_262781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 75680929) ^ 37840464 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 75680929) ^ 25226976 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 75680929) ^ 288 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_79030999 : Nat.Prime 79030999 := by
  apply lucas_primality 79030999 (13 : ZMod 79030999)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1463537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1463537, 1)] : List FactorBlock).map factorBlockValue).prod) = 79030999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_1463537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 79030999) ^ 39515499 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 79030999) ^ 26343666 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 79030999) ^ 54 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_85242719 : Nat.Prime 85242719 := by
  apply lucas_primality 85242719 (7 : ZMod 85242719)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3874669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3874669, 1)] : List FactorBlock).map factorBlockValue).prod) = 85242719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_3874669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 85242719) ^ 42621359 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85242719) ^ 7749338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85242719) ^ 22 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_85289951 : Nat.Prime 85289951 := by
  apply lucas_primality 85289951 (13 : ZMod 85289951)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1705799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1705799, 1)] : List FactorBlock).map factorBlockValue).prod) = 85289951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_1705799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 85289951) ^ 42644975 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 85289951) ^ 17057990 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 85289951) ^ 50 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_85876853 : Nat.Prime 85876853 := by
  apply lucas_primality 85876853 (2 : ZMod 85876853)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (379, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (379, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 85876853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_379
      · exact prime_oneHundredFiftySevenEY_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85876853) ^ 42938426 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85876853) ^ 2320996 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85876853) ^ 226588 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85876853) ^ 56092 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_87250601 : Nat.Prime 87250601 := by
  apply lucas_primality 87250601 (6 : ZMod 87250601)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (436253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (436253, 1)] : List FactorBlock).map factorBlockValue).prod) = 87250601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_436253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 87250601) ^ 43625300 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 87250601) ^ 17450120 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 87250601) ^ 200 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_89693099 : Nat.Prime 89693099 := by
  apply lucas_primality 89693099 (6 : ZMod 89693099)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (59, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (59, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 89693099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 89693099) ^ 44846549 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89693099) ^ 8153918 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89693099) ^ 2085886 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89693099) ^ 1520222 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 89693099) ^ 55814 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_93922489 : Nat.Prime 93922489 := by
  apply lucas_primality 93922489 (7 : ZMod 93922489)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (118589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (118589, 1)] : List FactorBlock).map factorBlockValue).prod) = 93922489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_118589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 93922489) ^ 46961244 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 93922489) ^ 31307496 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 93922489) ^ 8538408 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 93922489) ^ 792 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_94963699 : Nat.Prime 94963699 := by
  apply lucas_primality 94963699 (2 : ZMod 94963699)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (983, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (983, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 94963699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_983
      · exact prime_oneHundredFiftySevenEY_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94963699) ^ 47481849 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 94963699) ^ 31654566 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 94963699) ^ 96606 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 94963699) ^ 53082 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_96313439 : Nat.Prime 96313439 := by
  apply lucas_primality 96313439 (17 : ZMod 96313439)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (67, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (67, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) = 96313439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_4253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 96313439) ^ 48156719 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 96313439) ^ 7408726 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 96313439) ^ 1437514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 96313439) ^ 22646 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_98165591 : Nat.Prime 98165591 := by
  apply lucas_primality 98165591 (23 : ZMod 98165591)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (193, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (193, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) = 98165591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_193
      · exact prime_oneHundredFiftySevenEY_2677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 98165591) ^ 49082795 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (23 : ZMod 98165591) ^ 19633118 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (23 : ZMod 98165591) ^ 5166610 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (23 : ZMod 98165591) ^ 508630 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (23 : ZMod 98165591) ^ 36670 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_100186973 : Nat.Prime 100186973 := by
  apply lucas_primality 100186973 (2 : ZMod 100186973)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (163, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (163, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100186973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_163
      · exact prime_oneHundredFiftySevenEY_4153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100186973) ^ 50093486 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 100186973) ^ 2707756 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 100186973) ^ 614644 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 100186973) ^ 24124 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_108630077 : Nat.Prime 108630077 := by
  apply lucas_primality 108630077 (2 : ZMod 108630077)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 1), (23677, 1)] : List FactorBlock).map factorBlockValue).prod) = 108630077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_23677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108630077) ^ 54315038 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108630077) ^ 3504196 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108630077) ^ 2935948 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108630077) ^ 4588 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_120300667 : Nat.Prime 120300667 := by
  apply lucas_primality 120300667 (2 : ZMod 120300667)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1055269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1055269, 1)] : List FactorBlock).map factorBlockValue).prod) = 120300667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_1055269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120300667) ^ 60150333 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120300667) ^ 40100222 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120300667) ^ 6331614 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120300667) ^ 114 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_124980371 : Nat.Prime 124980371 := by
  apply lucas_primality 124980371 (2 : ZMod 124980371)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (281, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (281, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) = 124980371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_79
      · exact prime_oneHundredFiftySevenEY_281
      · exact prime_oneHundredFiftySevenEY_563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 124980371) ^ 62490185 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 124980371) ^ 24996074 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 124980371) ^ 1582030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 124980371) ^ 444770 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 124980371) ^ 221990 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_130747447 : Nat.Prime 130747447 := by
  apply lucas_primality 130747447 (3 : ZMod 130747447)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (807083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (807083, 1)] : List FactorBlock).map factorBlockValue).prod) = 130747447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_807083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 130747447) ^ 65373723 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 130747447) ^ 43582482 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 130747447) ^ 162 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_137961667 : Nat.Prime 137961667 := by
  apply lucas_primality 137961667 (3 : ZMod 137961667)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7664537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7664537, 1)] : List FactorBlock).map factorBlockValue).prod) = 137961667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7664537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 137961667) ^ 68980833 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 137961667) ^ 45987222 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 137961667) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_187888213 : Nat.Prime 187888213 := by
  apply lucas_primality 187888213 (2 : ZMod 187888213)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5219117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5219117, 1)] : List FactorBlock).map factorBlockValue).prod) = 187888213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5219117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 187888213) ^ 93944106 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 187888213) ^ 62629404 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 187888213) ^ 36 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_193386629 : Nat.Prime 193386629 := by
  apply lucas_primality 193386629 (2 : ZMod 193386629)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (79, 1), (35999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (79, 1), (35999, 1)] : List FactorBlock).map factorBlockValue).prod) = 193386629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_79
      · exact prime_oneHundredFiftySevenEY_35999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193386629) ^ 96693314 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386629) ^ 11375684 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386629) ^ 2447932 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 193386629) ^ 5372 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_193908391 : Nat.Prime 193908391 := by
  apply lucas_primality 193908391 (3 : ZMod 193908391)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (421, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (421, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) = 193908391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_421
      · exact prime_oneHundredFiftySevenEY_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 193908391) ^ 96954195 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 193908391) ^ 64636130 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 193908391) ^ 38781678 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 193908391) ^ 14916030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 193908391) ^ 460590 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 193908391) ^ 164190 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_213247379 : Nat.Prime 213247379 := by
  apply lucas_primality 213247379 (2 : ZMod 213247379)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (541237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (541237, 1)] : List FactorBlock).map factorBlockValue).prod) = 213247379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_197
      · exact prime_oneHundredFiftySevenEY_541237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 213247379) ^ 106623689 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 213247379) ^ 1082474 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 213247379) ^ 394 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_214827757 : Nat.Prime 214827757 := by
  apply lucas_primality 214827757 (5 : ZMod 214827757)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (13, 1), (19, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (13, 1), (19, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 214827757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 214827757) ^ 107413878 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 214827757) ^ 71609252 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 214827757) ^ 19529796 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 214827757) ^ 16525212 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 214827757) ^ 11306724 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 214827757) ^ 358644 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_220349681 : Nat.Prime 220349681 := by
  apply lucas_primality 220349681 (3 : ZMod 220349681)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (101, 1), (27271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (101, 1), (27271, 1)] : List FactorBlock).map factorBlockValue).prod) = 220349681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_27271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 220349681) ^ 110174840 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 220349681) ^ 44069936 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 220349681) ^ 2181680 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 220349681) ^ 8080 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_233264201 : Nat.Prime 233264201 := by
  apply lucas_primality 233264201 (3 : ZMod 233264201)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (73, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (73, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 233264201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_73
      · exact prime_oneHundredFiftySevenEY_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 233264201) ^ 116632100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 233264201) ^ 46652840 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 233264201) ^ 17943400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 233264201) ^ 3195400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 233264201) ^ 189800 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_238719527 : Nat.Prime 238719527 := by
  apply lucas_primality 238719527 (5 : ZMod 238719527)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (67, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (67, 1), (33613, 1)] : List FactorBlock).map factorBlockValue).prod) = 238719527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_53
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_33613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 238719527) ^ 119359763 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 238719527) ^ 4504142 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 238719527) ^ 3562978 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 238719527) ^ 7102 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_299887261 : Nat.Prime 299887261 := by
  apply lucas_primality 299887261 (10 : ZMod 299887261)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (47, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (29, 1), (47, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 299887261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 299887261) ^ 149943630 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 99962420 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 59977452 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 15783540 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 10340940 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 6380580 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 299887261) ^ 1553820 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_308280169 : Nat.Prime 308280169 := by
  apply lucas_primality 308280169 (11 : ZMod 308280169)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (7, 3), (19, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (7, 3), (19, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 308280169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 308280169) ^ 154140084 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 308280169) ^ 102760056 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 308280169) ^ 44040024 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 308280169) ^ 16225272 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 308280169) ^ 4223016 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_323998369 : Nat.Prime 323998369 := by
  apply lucas_primality 323998369 (11 : ZMod 323998369)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (3374983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (3374983, 1)] : List FactorBlock).map factorBlockValue).prod) = 323998369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_3374983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 323998369) ^ 161999184 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 323998369) ^ 107999456 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 323998369) ^ 96 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_341689847 : Nat.Prime 341689847 := by
  apply lucas_primality 341689847 (5 : ZMod 341689847)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (491, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (491, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 341689847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_349
      · exact prime_oneHundredFiftySevenEY_491
      · exact prime_oneHundredFiftySevenEY_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 341689847) ^ 170844923 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 341689847) ^ 979054 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 341689847) ^ 695906 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 341689847) ^ 342718 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_373671049 : Nat.Prime 373671049 := by
  apply lucas_primality 373671049 (7 : ZMod 373671049)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (401, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (401, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 373671049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_401
      · exact prime_oneHundredFiftySevenEY_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 373671049) ^ 186835524 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 373671049) ^ 124557016 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 373671049) ^ 9113928 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 373671049) ^ 931848 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 373671049) ^ 394584 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_386773259 : Nat.Prime 386773259 := by
  apply lucas_primality 386773259 (2 : ZMod 386773259)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193386629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193386629, 1)] : List FactorBlock).map factorBlockValue).prod) = 386773259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_193386629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 386773259) ^ 193386629 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 386773259) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_420061879 : Nat.Prime 420061879 := by
  apply lucas_primality 420061879 (3 : ZMod 420061879)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23336771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23336771, 1)] : List FactorBlock).map factorBlockValue).prod) = 420061879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_23336771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 420061879) ^ 210030939 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 420061879) ^ 140020626 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 420061879) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17203
      · exact prime_oneHundredFiftySevenEY_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_777411659 : Nat.Prime 777411659 := by
  apply lucas_primality 777411659 (2 : ZMod 777411659)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (409, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (409, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) = 777411659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_103
      · exact prime_oneHundredFiftySevenEY_409
      · exact prime_oneHundredFiftySevenEY_9227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 777411659) ^ 388705829 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 777411659) ^ 7547686 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 777411659) ^ 1900762 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 777411659) ^ 84254 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_805879807 : Nat.Prime 805879807 := by
  apply lucas_primality 805879807 (3 : ZMod 805879807)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (703211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (703211, 1)] : List FactorBlock).map factorBlockValue).prod) = 805879807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_191
      · exact prime_oneHundredFiftySevenEY_703211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 805879807) ^ 402939903 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 805879807) ^ 268626602 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 805879807) ^ 4219266 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 805879807) ^ 1146 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1299272743 : Nat.Prime 1299272743 := by
  apply lucas_primality 1299272743 (3 : ZMod 1299272743)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (72181819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (72181819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299272743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_72181819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1299272743) ^ 649636371 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299272743) ^ 433090914 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299272743) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1300074757 : Nat.Prime 1300074757 := by
  apply lucas_primality 1300074757 (2 : ZMod 1300074757)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (3735847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (3735847, 1)] : List FactorBlock).map factorBlockValue).prod) = 1300074757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_3735847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1300074757) ^ 650037378 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1300074757) ^ 433358252 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1300074757) ^ 44830164 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1300074757) ^ 348 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1302904927 : Nat.Prime 1302904927 := by
  apply lucas_primality 1302904927 (6 : ZMod 1302904927)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (8042623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (8042623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1302904927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_8042623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1302904927) ^ 651452463 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1302904927) ^ 434301642 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1302904927) ^ 162 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1431883433 : Nat.Prime 1431883433 := by
  apply lucas_primality 1431883433 (3 : ZMod 1431883433)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (25569347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (25569347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1431883433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_25569347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1431883433) ^ 715941716 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1431883433) ^ 204554776 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1431883433) ^ 56 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1568178377 : Nat.Prime 1568178377 := by
  apply lucas_primality 1568178377 (3 : ZMod 1568178377)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (2281, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (2281, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1568178377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_2281
      · exact prime_oneHundredFiftySevenEY_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1568178377) ^ 784089188 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1568178377) ^ 82535704 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1568178377) ^ 687496 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1568178377) ^ 346712 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1836642739 : Nat.Prime 1836642739 := by
  apply lucas_primality 1836642739 (2 : ZMod 1836642739)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43729589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43729589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1836642739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_43729589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1836642739) ^ 918321369 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1836642739) ^ 612214246 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1836642739) ^ 262377534 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1836642739) ^ 42 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2009515733 : Nat.Prime 2009515733 := by
  apply lucas_primality 2009515733 (3 : ZMod 2009515733)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (43, 1), (79, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (43, 1), (79, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2009515733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_79
      · exact prime_oneHundredFiftySevenEY_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2009515733) ^ 1004757866 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2009515733) ^ 287073676 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2009515733) ^ 54311236 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2009515733) ^ 46732924 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2009515733) ^ 25436908 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2009515733) ^ 3519292 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2094075119 : Nat.Prime 2094075119 := by
  apply lucas_primality 2094075119 (11 : ZMod 2094075119)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (883, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (883, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 2094075119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_601
      · exact prime_oneHundredFiftySevenEY_883
      · exact prime_oneHundredFiftySevenEY_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2094075119) ^ 1047037559 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 2094075119) ^ 3484318 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 2094075119) ^ 2371546 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 2094075119) ^ 1061366 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2306701459 : Nat.Prime 2306701459 := by
  apply lucas_primality 2306701459 (2 : ZMod 2306701459)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (2100821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (2100821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2306701459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_2100821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2306701459) ^ 1153350729 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306701459) ^ 768900486 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306701459) ^ 37814778 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306701459) ^ 1098 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2560774057 : Nat.Prime 2560774057 := by
  apply lucas_primality 2560774057 (5 : ZMod 2560774057)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (6276407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (6276407, 1)] : List FactorBlock).map factorBlockValue).prod) = 2560774057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_6276407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2560774057) ^ 1280387028 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2560774057) ^ 853591352 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2560774057) ^ 150633768 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2560774057) ^ 408 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2649842383 : Nat.Prime 2649842383 := by
  apply lucas_primality 2649842383 (3 : ZMod 2649842383)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (41, 1), (883, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (41, 1), (883, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2649842383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_883
      · exact prime_oneHundredFiftySevenEY_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2649842383) ^ 1324921191 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2649842383) ^ 883280794 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2649842383) ^ 240894762 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2649842383) ^ 64630302 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2649842383) ^ 3000954 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2649842383) ^ 2389398 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2804623001 : Nat.Prime 2804623001 := by
  apply lucas_primality 2804623001 (3 : ZMod 2804623001)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (661, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (661, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2804623001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_661
      · exact prime_oneHundredFiftySevenEY_4243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2804623001) ^ 1402311500 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2804623001) ^ 560924600 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2804623001) ^ 4243000 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2804623001) ^ 661000 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2824750043 : Nat.Prime 2824750043 := by
  apply lucas_primality 2824750043 (2 : ZMod 2824750043)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (757, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (757, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2824750043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_109
      · exact prime_oneHundredFiftySevenEY_757
      · exact prime_oneHundredFiftySevenEY_17117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2824750043) ^ 1412375021 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2824750043) ^ 25915138 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2824750043) ^ 3731506 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2824750043) ^ 165026 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2922931313 : Nat.Prime 2922931313 := by
  apply lucas_primality 2922931313 (3 : ZMod 2922931313)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (1535153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (1535153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2922931313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_1535153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2922931313) ^ 1461465656 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2922931313) ^ 417561616 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2922931313) ^ 171937136 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2922931313) ^ 1904 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3215386423 : Nat.Prime 3215386423 := by
  apply lucas_primality 3215386423 (3 : ZMod 3215386423)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (109, 1), (337, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (109, 1), (337, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 3215386423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_109
      · exact prime_oneHundredFiftySevenEY_337
      · exact prime_oneHundredFiftySevenEY_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3215386423) ^ 1607693211 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3215386423) ^ 1071795474 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3215386423) ^ 29498958 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3215386423) ^ 9541206 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3215386423) ^ 1983582 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3330836407 : Nat.Prime 3330836407 := by
  apply lucas_primality 3330836407 (6 : ZMod 3330836407)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (587, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (587, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330836407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_239
      · exact prime_oneHundredFiftySevenEY_587
      · exact prime_oneHundredFiftySevenEY_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3330836407) ^ 1665418203 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330836407) ^ 1110278802 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330836407) ^ 13936554 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330836407) ^ 5674338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3330836407) ^ 2525274 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3367019941 : Nat.Prime 3367019941 := by
  apply lucas_primality 3367019941 (2 : ZMod 3367019941)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3767, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3767, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod) = 3367019941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_3767
      · exact prime_oneHundredFiftySevenEY_14897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3367019941) ^ 1683509970 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3367019941) ^ 1122339980 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3367019941) ^ 673403988 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3367019941) ^ 893820 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3367019941) ^ 226020 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3489885617 : Nat.Prime 3489885617 := by
  apply lucas_primality 3489885617 (3 : ZMod 3489885617)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (181, 1), (172153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (181, 1), (172153, 1)] : List FactorBlock).map factorBlockValue).prod) = 3489885617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_181
      · exact prime_oneHundredFiftySevenEY_172153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3489885617) ^ 1744942808 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3489885617) ^ 498555088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3489885617) ^ 19281136 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3489885617) ^ 20272 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3560360449 : Nat.Prime 3560360449 := by
  apply lucas_primality 3560360449 (22 : ZMod 3560360449)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (19, 1), (121997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (19, 1), (121997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3560360449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_121997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 3560360449) ^ 1780180224 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (22 : ZMod 3560360449) ^ 1186786816 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (22 : ZMod 3560360449) ^ 187387392 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (22 : ZMod 3560360449) ^ 29184 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3699712619 : Nat.Prime 3699712619 := by
  apply lucas_primality 3699712619 (7 : ZMod 3699712619)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (101, 1), (153911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (101, 1), (153911, 1)] : List FactorBlock).map factorBlockValue).prod) = 3699712619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_153911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3699712619) ^ 1849856309 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3699712619) ^ 528530374 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3699712619) ^ 217630154 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3699712619) ^ 36630818 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3699712619) ^ 24038 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3733924279 : Nat.Prime 3733924279 := by
  apply lucas_primality 3733924279 (3 : ZMod 3733924279)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (331, 1), (337, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (331, 1), (337, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3733924279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_331
      · exact prime_oneHundredFiftySevenEY_337
      · exact prime_oneHundredFiftySevenEY_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3733924279) ^ 1866962139 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733924279) ^ 1244641426 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733924279) ^ 533417754 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733924279) ^ 11280738 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733924279) ^ 11079894 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733924279) ^ 4684974 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4384591597 : Nat.Prime 4384591597 := by
  apply lucas_primality 4384591597 (2 : ZMod 4384591597)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (1581743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (1581743, 1)] : List FactorBlock).map factorBlockValue).prod) = 4384591597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_1581743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4384591597) ^ 2192295798 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4384591597) ^ 1461530532 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4384591597) ^ 626370228 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4384591597) ^ 398599236 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4384591597) ^ 2772 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4574292847 : Nat.Prime 4574292847 := by
  apply lucas_primality 4574292847 (3 : ZMod 4574292847)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (131, 1), (70117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (131, 1), (70117, 1)] : List FactorBlock).map factorBlockValue).prod) = 4574292847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_83
      · exact prime_oneHundredFiftySevenEY_131
      · exact prime_oneHundredFiftySevenEY_70117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4574292847) ^ 2287146423 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4574292847) ^ 1524764282 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4574292847) ^ 55111962 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4574292847) ^ 34918266 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4574292847) ^ 65238 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_5655094199 : Nat.Prime 5655094199 := by
  apply lucas_primality 5655094199 (31 : ZMod 5655094199)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (131, 1), (239, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (131, 1), (239, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) = 5655094199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_131
      · exact prime_oneHundredFiftySevenEY_239
      · exact prime_oneHundredFiftySevenEY_6947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 5655094199) ^ 2827547099 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (31 : ZMod 5655094199) ^ 435007246 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (31 : ZMod 5655094199) ^ 43168658 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (31 : ZMod 5655094199) ^ 23661482 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (31 : ZMod 5655094199) ^ 814034 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7067922553 : Nat.Prime 7067922553 := by
  apply lucas_primality 7067922553 (5 : ZMod 7067922553)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (98165591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (98165591, 1)] : List FactorBlock).map factorBlockValue).prod) = 7067922553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_98165591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7067922553) ^ 3533961276 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7067922553) ^ 2355974184 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7067922553) ^ 72 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7399425239 : Nat.Prime 7399425239 := by
  apply lucas_primality 7399425239 (13 : ZMod 7399425239)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3699712619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3699712619, 1)] : List FactorBlock).map factorBlockValue).prod) = 7399425239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3699712619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 7399425239) ^ 3699712619 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 7399425239) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7701644099 : Nat.Prime 7701644099 := by
  apply lucas_primality 7701644099 (2 : ZMod 7701644099)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (93922489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (93922489, 1)] : List FactorBlock).map factorBlockValue).prod) = 7701644099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_93922489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7701644099) ^ 3850822049 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7701644099) ^ 187844978 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7701644099) ^ 82 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7735465181 : Nat.Prime 7735465181 := by
  apply lucas_primality 7735465181 (2 : ZMod 7735465181)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (386773259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (386773259, 1)] : List FactorBlock).map factorBlockValue).prod) = 7735465181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_386773259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7735465181) ^ 3867732590 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7735465181) ^ 1547093036 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7735465181) ^ 20 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7891304947 : Nat.Prime 7891304947 := by
  apply lucas_primality 7891304947 (2 : ZMod 7891304947)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (187888213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (187888213, 1)] : List FactorBlock).map factorBlockValue).prod) = 7891304947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_187888213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7891304947) ^ 3945652473 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891304947) ^ 2630434982 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891304947) ^ 1127329278 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7891304947) ^ 42 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_8331488861 : Nat.Prime 8331488861 := by
  apply lucas_primality 8331488861 (2 : ZMod 8331488861)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (67, 1), (487, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (67, 1), (487, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 8331488861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_487
      · exact prime_oneHundredFiftySevenEY_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8331488861) ^ 4165744430 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8331488861) ^ 1666297772 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8331488861) ^ 490087580 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8331488861) ^ 124350580 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8331488861) ^ 17107780 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8331488861) ^ 11093860 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_9484948073 : Nat.Prime 9484948073 := by
  apply lucas_primality 9484948073 (3 : ZMod 9484948073)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 2), (318629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 2), (318629, 1)] : List FactorBlock).map factorBlockValue).prod) = 9484948073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_318629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9484948073) ^ 4742474036 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9484948073) ^ 155490952 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9484948073) ^ 29768 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_9908192201 : Nat.Prime 9908192201 := by
  apply lucas_primality 9908192201 (6 : ZMod 9908192201)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (19, 1), (29, 1), (47, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (19, 1), (29, 1), (47, 1), (1913, 1)] : List FactorBlock).map factorBlockValue).prod) = 9908192201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_1913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9908192201) ^ 4954096100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9908192201) ^ 1981638440 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9908192201) ^ 521483800 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9908192201) ^ 341661800 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9908192201) ^ 210812600 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 9908192201) ^ 5179400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_9912904907 : Nat.Prime 9912904907 := by
  apply lucas_primality 9912904907 (2 : ZMod 9912904907)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (89, 1), (457, 1), (3931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (89, 1), (457, 1), (3931, 1)] : List FactorBlock).map factorBlockValue).prod) = 9912904907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_89
      · exact prime_oneHundredFiftySevenEY_457
      · exact prime_oneHundredFiftySevenEY_3931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9912904907) ^ 4956452453 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9912904907) ^ 319771126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9912904907) ^ 111380954 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9912904907) ^ 21691258 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9912904907) ^ 2521726 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_10119682693 : Nat.Prime 10119682693 := by
  apply lucas_primality 10119682693 (5 : ZMod 10119682693)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (631, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (631, 1), (2767, 1)] : List FactorBlock).map factorBlockValue).prod) = 10119682693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_631
      · exact prime_oneHundredFiftySevenEY_2767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10119682693) ^ 5059841346 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 10119682693) ^ 3373227564 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 10119682693) ^ 1445668956 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 10119682693) ^ 439986204 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 10119682693) ^ 16037532 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 10119682693) ^ 3657276 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_10136509739 : Nat.Prime 10136509739 := by
  apply lucas_primality 10136509739 (2 : ZMod 10136509739)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (44851813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (44851813, 1)] : List FactorBlock).map factorBlockValue).prod) = 10136509739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_113
      · exact prime_oneHundredFiftySevenEY_44851813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10136509739) ^ 5068254869 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10136509739) ^ 89703626 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 10136509739) ^ 226 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_12037053029 : Nat.Prime 12037053029 := by
  apply lucas_primality 12037053029 (10 : ZMod 12037053029)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (13, 1), (1453, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (13, 1), (1453, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) = 12037053029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_1453
      · exact prime_oneHundredFiftySevenEY_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12037053029) ^ 6018526514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 12037053029) ^ 1719579004 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 12037053029) ^ 1094277548 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 12037053029) ^ 925927156 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 12037053029) ^ 8284276 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 12037053029) ^ 5817812 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_12595475021 : Nat.Prime 12595475021 := by
  apply lucas_primality 12595475021 (2 : ZMod 12595475021)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (263, 1), (617, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (263, 1), (617, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 12595475021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_263
      · exact prime_oneHundredFiftySevenEY_617
      · exact prime_oneHundredFiftySevenEY_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12595475021) ^ 6297737510 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 12595475021) ^ 2519095004 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 12595475021) ^ 47891540 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 12595475021) ^ 20414060 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 12595475021) ^ 3245420 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_13429776301 : Nat.Prime 13429776301 := by
  apply lucas_primality 13429776301 (2 : ZMod 13429776301)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1087, 1), (41183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1087, 1), (41183, 1)] : List FactorBlock).map factorBlockValue).prod) = 13429776301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_1087
      · exact prime_oneHundredFiftySevenEY_41183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13429776301) ^ 6714888150 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13429776301) ^ 4476592100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13429776301) ^ 2685955260 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13429776301) ^ 12354900 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13429776301) ^ 326100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_13484845259 : Nat.Prime 13484845259 := by
  apply lucas_primality 13484845259 (2 : ZMod 13484845259)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (94963699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (94963699, 1)] : List FactorBlock).map factorBlockValue).prod) = 13484845259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_71
      · exact prime_oneHundredFiftySevenEY_94963699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13484845259) ^ 6742422629 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13484845259) ^ 189927398 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 13484845259) ^ 142 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_13646312047 : Nat.Prime 13646312047 := by
  apply lucas_primality 13646312047 (3 : ZMod 13646312047)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (44595791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (44595791, 1)] : List FactorBlock).map factorBlockValue).prod) = 13646312047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_44595791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13646312047) ^ 6823156023 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13646312047) ^ 4548770682 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13646312047) ^ 802724238 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13646312047) ^ 306 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_15159420433 : Nat.Prime 15159420433 := by
  apply lucas_primality 15159420433 (5 : ZMod 15159420433)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (13, 1), (2699327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (13, 1), (2699327, 1)] : List FactorBlock).map factorBlockValue).prod) = 15159420433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_2699327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15159420433) ^ 7579710216 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 15159420433) ^ 5053140144 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 15159420433) ^ 1166109264 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 15159420433) ^ 5616 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_17219769491 : Nat.Prime 17219769491 := by
  apply lucas_primality 17219769491 (6 : ZMod 17219769491)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (972319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (23, 1), (972319, 1)] : List FactorBlock).map factorBlockValue).prod) = 17219769491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_972319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17219769491) ^ 8609884745 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 17219769491) ^ 3443953898 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 17219769491) ^ 2459967070 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 17219769491) ^ 1565433590 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 17219769491) ^ 748685630 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 17219769491) ^ 17710 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_17538366389 : Nat.Prime 17538366389 := by
  apply lucas_primality 17538366389 (2 : ZMod 17538366389)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4384591597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4384591597, 1)] : List FactorBlock).map factorBlockValue).prod) = 17538366389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_4384591597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 17538366389) ^ 8769183194 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17538366389) ^ 4 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_17843142601 : Nat.Prime 17843142601 := by
  apply lucas_primality 17843142601 (13 : ZMod 17843142601)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (41, 2), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (41, 2), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 17843142601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 17843142601) ^ 8921571300 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 17843142601) ^ 5947714200 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 17843142601) ^ 3568628520 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 17843142601) ^ 435198600 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 17843142601) ^ 3025800 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_19616688731 : Nat.Prime 19616688731 := by
  apply lucas_primality 19616688731 (2 : ZMod 19616688731)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (85289951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (85289951, 1)] : List FactorBlock).map factorBlockValue).prod) = 19616688731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_85289951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19616688731) ^ 9808344365 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19616688731) ^ 3923337746 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19616688731) ^ 852899510 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19616688731) ^ 230 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_20692877189 : Nat.Prime 20692877189 := by
  apply lucas_primality 20692877189 (2 : ZMod 20692877189)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (211, 1), (415553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (211, 1), (415553, 1)] : List FactorBlock).map factorBlockValue).prod) = 20692877189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_211
      · exact prime_oneHundredFiftySevenEY_415553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20692877189) ^ 10346438594 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20692877189) ^ 350726732 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20692877189) ^ 98070508 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20692877189) ^ 49796 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_24074106059 : Nat.Prime 24074106059 := by
  apply lucas_primality 24074106059 (2 : ZMod 24074106059)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12037053029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12037053029, 1)] : List FactorBlock).map factorBlockValue).prod) = 24074106059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_12037053029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 24074106059) ^ 12037053029 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24074106059) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_26969690519 : Nat.Prime 26969690519 := by
  apply lucas_primality 26969690519 (7 : ZMod 26969690519)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13484845259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13484845259, 1)] : List FactorBlock).map factorBlockValue).prod) = 26969690519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13484845259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 26969690519) ^ 13484845259 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 26969690519) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_28874932649 : Nat.Prime 28874932649 := by
  apply lucas_primality 28874932649 (3 : ZMod 28874932649)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (773, 1), (69691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (773, 1), (69691, 1)] : List FactorBlock).map factorBlockValue).prod) = 28874932649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_773
      · exact prime_oneHundredFiftySevenEY_69691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28874932649) ^ 14437466324 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 28874932649) ^ 430969144 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 28874932649) ^ 37354376 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 28874932649) ^ 414328 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_29193988861 : Nat.Prime 29193988861 := by
  apply lucas_primality 29193988861 (2 : ZMod 29193988861)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (2591, 1), (62597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (2591, 1), (62597, 1)] : List FactorBlock).map factorBlockValue).prod) = 29193988861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_2591
      · exact prime_oneHundredFiftySevenEY_62597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29193988861) ^ 14596994430 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29193988861) ^ 9731329620 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29193988861) ^ 5838797772 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29193988861) ^ 11267460 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 29193988861) ^ 466380 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_34439538983 : Nat.Prime 34439538983 := by
  apply lucas_primality 34439538983 (5 : ZMod 34439538983)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17219769491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17219769491, 1)] : List FactorBlock).map factorBlockValue).prod) = 34439538983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17219769491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 34439538983) ^ 17219769491 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 34439538983) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_35830214219 : Nat.Prime 35830214219 := by
  apply lucas_primality 35830214219 (2 : ZMod 35830214219)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7151, 1), (2505259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7151, 1), (2505259, 1)] : List FactorBlock).map factorBlockValue).prod) = 35830214219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7151
      · exact prime_oneHundredFiftySevenEY_2505259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35830214219) ^ 17915107109 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 35830214219) ^ 5010518 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 35830214219) ^ 14302 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_36110273473 : Nat.Prime 36110273473 := by
  apply lucas_primality 36110273473 (5 : ZMod 36110273473)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (7, 1), (13, 1), (229639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (7, 1), (13, 1), (229639, 1)] : List FactorBlock).map factorBlockValue).prod) = 36110273473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_229639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36110273473) ^ 18055136736 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36110273473) ^ 12036757824 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36110273473) ^ 5158610496 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36110273473) ^ 2777713344 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36110273473) ^ 157248 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_37080189299 : Nat.Prime 37080189299 := by
  apply lucas_primality 37080189299 (2 : ZMod 37080189299)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25867, 1), (716747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25867, 1), (716747, 1)] : List FactorBlock).map factorBlockValue).prod) = 37080189299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_25867
      · exact prime_oneHundredFiftySevenEY_716747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37080189299) ^ 18540094649 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37080189299) ^ 1433494 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37080189299) ^ 51734 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_37802782117 : Nat.Prime 37802782117 := by
  apply lucas_primality 37802782117 (2 : ZMod 37802782117)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (41, 1), (2328331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (41, 1), (2328331, 1)] : List FactorBlock).map factorBlockValue).prod) = 37802782117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_2328331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37802782117) ^ 18901391058 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37802782117) ^ 12600927372 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37802782117) ^ 3436616556 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37802782117) ^ 922019076 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37802782117) ^ 16236 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_38918331239 : Nat.Prime 38918331239 := by
  apply lucas_primality 38918331239 (7 : ZMod 38918331239)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (131, 1), (5122181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (131, 1), (5122181, 1)] : List FactorBlock).map factorBlockValue).prod) = 38918331239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_131
      · exact prime_oneHundredFiftySevenEY_5122181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 38918331239) ^ 19459165619 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 38918331239) ^ 1342011422 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 38918331239) ^ 297086498 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 38918331239) ^ 7598 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_44832779351 : Nat.Prime 44832779351 := by
  apply lucas_primality 44832779351 (19 : ZMod 44832779351)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1307, 1), (686041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1307, 1), (686041, 1)] : List FactorBlock).map factorBlockValue).prod) = 44832779351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_1307
      · exact prime_oneHundredFiftySevenEY_686041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 44832779351) ^ 22416389675 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 44832779351) ^ 8966555870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 44832779351) ^ 34302050 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 44832779351) ^ 65350 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_47509365017 : Nat.Prime 47509365017 := by
  apply lucas_primality 47509365017 (3 : ZMod 47509365017)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5087, 1), (1167421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5087, 1), (1167421, 1)] : List FactorBlock).map factorBlockValue).prod) = 47509365017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5087
      · exact prime_oneHundredFiftySevenEY_1167421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47509365017) ^ 23754682508 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 47509365017) ^ 9339368 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 47509365017) ^ 40696 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_48071526703 : Nat.Prime 48071526703 := by
  apply lucas_primality 48071526703 (3 : ZMod 48071526703)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (509, 1), (199247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (509, 1), (199247, 1)] : List FactorBlock).map factorBlockValue).prod) = 48071526703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_79
      · exact prime_oneHundredFiftySevenEY_509
      · exact prime_oneHundredFiftySevenEY_199247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48071526703) ^ 24035763351 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 48071526703) ^ 16023842234 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 48071526703) ^ 608500338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 48071526703) ^ 94443078 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 48071526703) ^ 241266 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_50113472137 : Nat.Prime 50113472137 := by
  apply lucas_primality 50113472137 (5 : ZMod 50113472137)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (47, 1), (488207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (47, 1), (488207, 1)] : List FactorBlock).map factorBlockValue).prod) = 50113472137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_488207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50113472137) ^ 25056736068 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50113472137) ^ 16704490712 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50113472137) ^ 7159067448 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50113472137) ^ 3854882472 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50113472137) ^ 1066244088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 50113472137) ^ 102648 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_52133239439 : Nat.Prime 52133239439 := by
  apply lucas_primality 52133239439 (7 : ZMod 52133239439)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (71, 1), (7492561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (71, 1), (7492561, 1)] : List FactorBlock).map factorBlockValue).prod) = 52133239439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_71
      · exact prime_oneHundredFiftySevenEY_7492561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 52133239439) ^ 26066619719 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 52133239439) ^ 7447605634 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 52133239439) ^ 734270978 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 52133239439) ^ 6958 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_60637681733 : Nat.Prime 60637681733 := by
  apply lucas_primality 60637681733 (2 : ZMod 60637681733)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15159420433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15159420433, 1)] : List FactorBlock).map factorBlockValue).prod) = 60637681733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_15159420433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 60637681733) ^ 30318840866 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 60637681733) ^ 4 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_72383934739 : Nat.Prime 72383934739 := by
  apply lucas_primality 72383934739 (2 : ZMod 72383934739)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (1523, 1), (27409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (1523, 1), (27409, 1)] : List FactorBlock).map factorBlockValue).prod) = 72383934739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_1523
      · exact prime_oneHundredFiftySevenEY_27409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72383934739) ^ 36191967369 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72383934739) ^ 24127978246 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72383934739) ^ 4257878514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72383934739) ^ 47527206 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 72383934739) ^ 2640882 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_73727727379 : Nat.Prime 73727727379 := by
  apply lucas_primality 73727727379 (2 : ZMod 73727727379)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (89693099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (89693099, 1)] : List FactorBlock).map factorBlockValue).prod) = 73727727379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_137
      · exact prime_oneHundredFiftySevenEY_89693099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73727727379) ^ 36863863689 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73727727379) ^ 24575909126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73727727379) ^ 538158594 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73727727379) ^ 822 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_87669271957 : Nat.Prime 87669271957 := by
  apply lucas_primality 87669271957 (2 : ZMod 87669271957)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (127, 1), (8217967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (127, 1), (8217967, 1)] : List FactorBlock).map factorBlockValue).prod) = 87669271957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_127
      · exact prime_oneHundredFiftySevenEY_8217967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87669271957) ^ 43834635978 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669271957) ^ 29223090652 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669271957) ^ 12524181708 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669271957) ^ 690309228 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669271957) ^ 10668 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_97877448247 : Nat.Prime 97877448247 := by
  apply lucas_primality 97877448247 (6 : ZMod 97877448247)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (617, 1), (261773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (617, 1), (261773, 1)] : List FactorBlock).map factorBlockValue).prod) = 97877448247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_617
      · exact prime_oneHundredFiftySevenEY_261773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 97877448247) ^ 48938724123 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 97877448247) ^ 32625816082 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 97877448247) ^ 969083646 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 97877448247) ^ 158634438 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 97877448247) ^ 373902 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_102634142683 : Nat.Prime 102634142683 := by
  apply lucas_primality 102634142683 (2 : ZMod 102634142683)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9281, 1), (1843087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9281, 1), (1843087, 1)] : List FactorBlock).map factorBlockValue).prod) = 102634142683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_9281
      · exact prime_oneHundredFiftySevenEY_1843087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102634142683) ^ 51317071341 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102634142683) ^ 34211380894 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102634142683) ^ 11058522 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102634142683) ^ 55686 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_121275363467 : Nat.Prime 121275363467 := by
  apply lucas_primality 121275363467 (2 : ZMod 121275363467)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60637681733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60637681733, 1)] : List FactorBlock).map factorBlockValue).prod) = 121275363467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_60637681733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 121275363467) ^ 60637681733 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 121275363467) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_154298644033 : Nat.Prime 154298644033 := by
  apply lucas_primality 154298644033 (5 : ZMod 154298644033)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 2), (277, 1), (17167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 2), (277, 1), (17167, 1)] : List FactorBlock).map factorBlockValue).prod) = 154298644033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_277
      · exact prime_oneHundredFiftySevenEY_17167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 154298644033) ^ 77149322016 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 154298644033) ^ 51432881344 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 154298644033) ^ 11869126464 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 154298644033) ^ 557034816 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 154298644033) ^ 8988096 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_155264037697 : Nat.Prime 155264037697 := by
  apply lucas_primality 155264037697 (10 : ZMod 155264037697)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (17, 1), (15856213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (17, 1), (15856213, 1)] : List FactorBlock).map factorBlockValue).prod) = 155264037697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_15856213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 155264037697) ^ 77632018848 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 155264037697) ^ 51754679232 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 155264037697) ^ 9133178688 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 155264037697) ^ 9792 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_157154640991 : Nat.Prime 157154640991 := by
  apply lucas_primality 157154640991 (12 : ZMod 157154640991)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (85876853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (85876853, 1)] : List FactorBlock).map factorBlockValue).prod) = 157154640991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_85876853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 157154640991) ^ 78577320495 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 157154640991) ^ 52384880330 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 157154640991) ^ 31430928198 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 157154640991) ^ 2576305590 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 157154640991) ^ 1830 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_172057699381 : Nat.Prime 172057699381 := by
  apply lucas_primality 172057699381 (14 : ZMod 172057699381)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (17, 1), (281, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (17, 1), (281, 1), (12251, 1)] : List FactorBlock).map factorBlockValue).prod) = 172057699381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_281
      · exact prime_oneHundredFiftySevenEY_12251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 172057699381) ^ 86028849690 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 57352566460 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 34411539876 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 24579671340 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 10121041140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 612304980 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 172057699381) ^ 14044380 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_180402648431 : Nat.Prime 180402648431 := by
  apply lucas_primality 180402648431 (11 : ZMod 180402648431)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (409, 1), (1917749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (409, 1), (1917749, 1)] : List FactorBlock).map factorBlockValue).prod) = 180402648431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_409
      · exact prime_oneHundredFiftySevenEY_1917749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 180402648431) ^ 90201324215 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 180402648431) ^ 36080529686 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 180402648431) ^ 7843593410 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 180402648431) ^ 441082270 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 180402648431) ^ 94070 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_190112907169 : Nat.Prime 190112907169 := by
  apply lucas_primality 190112907169 (17 : ZMod 190112907169)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (811, 1), (90439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (811, 1), (90439, 1)] : List FactorBlock).map factorBlockValue).prod) = 190112907169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_811
      · exact prime_oneHundredFiftySevenEY_90439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 190112907169) ^ 95056453584 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 190112907169) ^ 63370969056 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 190112907169) ^ 234417888 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (17 : ZMod 190112907169) ^ 2102112 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_202004361829 : Nat.Prime 202004361829 := by
  apply lucas_primality 202004361829 (2 : ZMod 202004361829)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149, 1), (2417, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149, 1), (2417, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) = 202004361829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_149
      · exact prime_oneHundredFiftySevenEY_2417
      · exact prime_oneHundredFiftySevenEY_15581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 202004361829) ^ 101002180914 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 202004361829) ^ 67334787276 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 202004361829) ^ 1355733972 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 202004361829) ^ 83576484 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 202004361829) ^ 12964788 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_219504298613 : Nat.Prime 219504298613 := by
  apply lucas_primality 219504298613 (2 : ZMod 219504298613)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (193908391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (193908391, 1)] : List FactorBlock).map factorBlockValue).prod) = 219504298613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_283
      · exact prime_oneHundredFiftySevenEY_193908391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219504298613) ^ 109752149306 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 219504298613) ^ 775633564 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 219504298613) ^ 1132 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_294726714091 : Nat.Prime 294726714091 := by
  apply lucas_primality 294726714091 (2 : ZMod 294726714091)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (307, 1), (744203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (307, 1), (744203, 1)] : List FactorBlock).map factorBlockValue).prod) = 294726714091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_307
      · exact prime_oneHundredFiftySevenEY_744203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294726714091) ^ 147363357045 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294726714091) ^ 98242238030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294726714091) ^ 58945342818 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294726714091) ^ 6854109630 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294726714091) ^ 960021870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294726714091) ^ 396030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_310659864859 : Nat.Prime 310659864859 := by
  apply lucas_primality 310659864859 (2 : ZMod 310659864859)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (23, 1), (607, 1), (25229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (23, 1), (607, 1), (25229, 1)] : List FactorBlock).map factorBlockValue).prod) = 310659864859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_607
      · exact prime_oneHundredFiftySevenEY_25229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 310659864859) ^ 155329932429 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 310659864859) ^ 103553288286 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 310659864859) ^ 44379980694 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 310659864859) ^ 13506950646 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 310659864859) ^ 511795494 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 310659864859) ^ 12313602 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_311300838161 : Nat.Prime 311300838161 := by
  apply lucas_primality 311300838161 (6 : ZMod 311300838161)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (19, 1), (53, 1), (297247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (19, 1), (53, 1), (297247, 1)] : List FactorBlock).map factorBlockValue).prod) = 311300838161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_53
      · exact prime_oneHundredFiftySevenEY_297247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 311300838161) ^ 155650419080 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 311300838161) ^ 62260167632 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 311300838161) ^ 23946218320 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 311300838161) ^ 16384254640 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 311300838161) ^ 5873600720 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 311300838161) ^ 1047280 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_410536570733 : Nat.Prime 410536570733 := by
  apply lucas_primality 410536570733 (2 : ZMod 410536570733)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (102634142683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (102634142683, 1)] : List FactorBlock).map factorBlockValue).prod) = 410536570733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_102634142683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 410536570733) ^ 205268285366 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 410536570733) ^ 4 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_542589269587 : Nat.Prime 542589269587 := by
  apply lucas_primality 542589269587 (2 : ZMod 542589269587)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 2), (17, 1), (101, 1), (211, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 2), (17, 1), (101, 1), (211, 2)] : List FactorBlock).map factorBlockValue).prod) = 542589269587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 542589269587) ^ 271294634793 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 180863089862 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 77512752798 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 41737636122 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 31917015858 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 5372170986 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542589269587) ^ 2571513126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_637357217327 : Nat.Prime 637357217327 := by
  apply lucas_primality 637357217327 (5 : ZMod 637357217327)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (47, 1), (433, 1), (680831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (47, 1), (433, 1), (680831, 1)] : List FactorBlock).map factorBlockValue).prod) = 637357217327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_433
      · exact prime_oneHundredFiftySevenEY_680831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 637357217327) ^ 318678608663 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 637357217327) ^ 27711183362 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 637357217327) ^ 13560791858 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 637357217327) ^ 1471956622 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 637357217327) ^ 936146 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_705994234369 : Nat.Prime 705994234369 := by
  apply lucas_primality 705994234369 (11 : ZMod 705994234369)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (1327, 1), (346369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (1327, 1), (346369, 1)] : List FactorBlock).map factorBlockValue).prod) = 705994234369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_1327
      · exact prime_oneHundredFiftySevenEY_346369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 705994234369) ^ 352997117184 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 705994234369) ^ 235331411456 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 705994234369) ^ 532022784 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 705994234369) ^ 2038272 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_925791864199 : Nat.Prime 925791864199 := by
  apply lucas_primality 925791864199 (11 : ZMod 925791864199)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (154298644033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (154298644033, 1)] : List FactorBlock).map factorBlockValue).prod) = 925791864199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_154298644033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 925791864199) ^ 462895932099 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 925791864199) ^ 308597288066 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 925791864199) ^ 6 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_972275069837 : Nat.Prime 972275069837 := by
  apply lucas_primality 972275069837 (2 : ZMod 972275069837)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (337, 1), (14719843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (337, 1), (14719843, 1)] : List FactorBlock).map factorBlockValue).prod) = 972275069837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_337
      · exact prime_oneHundredFiftySevenEY_14719843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 972275069837) ^ 486137534918 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 972275069837) ^ 138896438548 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 972275069837) ^ 2885089228 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 972275069837) ^ 66052 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1019137047013 : Nat.Prime 1019137047013 := by
  apply lucas_primality 1019137047013 (5 : ZMod 1019137047013)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (19, 1), (101, 1), (234161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (19, 1), (101, 1), (234161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1019137047013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_101
      · exact prime_oneHundredFiftySevenEY_234161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1019137047013) ^ 509568523506 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019137047013) ^ 339712349004 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019137047013) ^ 145591006716 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019137047013) ^ 53638791948 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019137047013) ^ 10090465812 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019137047013) ^ 4352292 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1401311465329 : Nat.Prime 1401311465329 := by
  apply lucas_primality 1401311465329 (7 : ZMod 1401311465329)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29193988861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29193988861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1401311465329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_29193988861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1401311465329) ^ 700655732664 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1401311465329) ^ 467103821776 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1401311465329) ^ 48 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1440085660477 : Nat.Prime 1440085660477 := by
  apply lucas_primality 1440085660477 (14 : ZMod 1440085660477)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (167, 1), (311, 1), (34487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (167, 1), (311, 1), (34487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440085660477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_167
      · exact prime_oneHundredFiftySevenEY_311
      · exact prime_oneHundredFiftySevenEY_34487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1440085660477) ^ 720042830238 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 1440085660477) ^ 480028553492 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 1440085660477) ^ 21493815828 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 1440085660477) ^ 8623267428 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 1440085660477) ^ 4630500516 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (14 : ZMod 1440085660477) ^ 41757348 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1559547702281 : Nat.Prime 1559547702281 := by
  apply lucas_primality 1559547702281 (3 : ZMod 1559547702281)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (317, 1), (1637, 1), (75133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (317, 1), (1637, 1), (75133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1559547702281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_317
      · exact prime_oneHundredFiftySevenEY_1637
      · exact prime_oneHundredFiftySevenEY_75133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1559547702281) ^ 779773851140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1559547702281) ^ 311909540456 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1559547702281) ^ 4919708840 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1559547702281) ^ 952686440 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1559547702281) ^ 20757160 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1723214457317 : Nat.Prime 1723214457317 := by
  apply lucas_primality 1723214457317 (2 : ZMod 1723214457317)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (3560360449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (3560360449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1723214457317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_3560360449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1723214457317) ^ 861607228658 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1723214457317) ^ 156655859756 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1723214457317) ^ 484 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1768360284547 : Nat.Prime 1768360284547 := by
  apply lucas_primality 1768360284547 (2 : ZMod 1768360284547)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (294726714091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (294726714091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1768360284547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_294726714091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1768360284547) ^ 884180142273 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768360284547) ^ 589453428182 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768360284547) ^ 6 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2227845033587 : Nat.Prime 2227845033587 := by
  apply lucas_primality 2227845033587 (2 : ZMod 2227845033587)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (2083, 1), (767243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (2083, 1), (767243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2227845033587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_2083
      · exact prime_oneHundredFiftySevenEY_767243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2227845033587) ^ 1113922516793 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2227845033587) ^ 131049707858 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2227845033587) ^ 54337683746 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2227845033587) ^ 1069536742 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2227845033587) ^ 2903702 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2281283630737 : Nat.Prime 2281283630737 := by
  apply lucas_primality 2281283630737 (5 : ZMod 2281283630737)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (29, 1), (79, 1), (1885907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (29, 1), (79, 1), (1885907, 1)] : List FactorBlock).map factorBlockValue).prod) = 2281283630737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_79
      · exact prime_oneHundredFiftySevenEY_1885907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2281283630737) ^ 1140641815368 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2281283630737) ^ 760427876912 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2281283630737) ^ 207389420976 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2281283630737) ^ 78664952784 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2281283630737) ^ 28877007984 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2281283630737) ^ 1209648 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2514294307297 : Nat.Prime 2514294307297 := by
  apply lucas_primality 2514294307297 (7 : ZMod 2514294307297)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (53, 1), (661, 1), (249199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (53, 1), (661, 1), (249199, 1)] : List FactorBlock).map factorBlockValue).prod) = 2514294307297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_53
      · exact prime_oneHundredFiftySevenEY_661
      · exact prime_oneHundredFiftySevenEY_249199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2514294307297) ^ 1257147153648 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2514294307297) ^ 838098102432 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2514294307297) ^ 47439515232 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2514294307297) ^ 3803773536 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2514294307297) ^ 10089504 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2634051583357 : Nat.Prime 2634051583357 := by
  apply lucas_primality 2634051583357 (29 : ZMod 2634051583357)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (219504298613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (219504298613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2634051583357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_219504298613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (29 : ZMod 2634051583357) ^ 1317025791678 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 2634051583357) ^ 878017194452 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 2634051583357) ^ 12 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2858100133843 : Nat.Prime 2858100133843 := by
  apply lucas_primality 2858100133843 (2 : ZMod 2858100133843)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (521, 1), (967, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (521, 1), (967, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858100133843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_521
      · exact prime_oneHundredFiftySevenEY_967
      · exact prime_oneHundredFiftySevenEY_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2858100133843) ^ 1429050066921 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858100133843) ^ 952700044614 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858100133843) ^ 69709759362 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858100133843) ^ 5485796802 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858100133843) ^ 2955636126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2858100133843) ^ 371809566 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2942179252759 : Nat.Prime 2942179252759 := by
  apply lucas_primality 2942179252759 (3 : ZMod 2942179252759)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59, 1), (179, 1), (5159057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59, 1), (179, 1), (5159057, 1)] : List FactorBlock).map factorBlockValue).prod) = 2942179252759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_179
      · exact prime_oneHundredFiftySevenEY_5159057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2942179252759) ^ 1471089626379 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2942179252759) ^ 980726417586 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2942179252759) ^ 49867444962 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2942179252759) ^ 16436755602 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2942179252759) ^ 570294 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3125965941779 : Nat.Prime 3125965941779 := by
  apply lucas_primality 3125965941779 (2 : ZMod 3125965941779)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (1836642739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (1836642739, 1)] : List FactorBlock).map factorBlockValue).prod) = 3125965941779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_1836642739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3125965941779) ^ 1562982970889 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3125965941779) ^ 135911562686 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3125965941779) ^ 84485565994 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3125965941779) ^ 1702 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3300941532509 : Nat.Prime 3300941532509 := by
  apply lucas_primality 3300941532509 (2 : ZMod 3300941532509)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (47, 1), (199, 1), (5190127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (47, 1), (199, 1), (5190127, 1)] : List FactorBlock).map factorBlockValue).prod) = 3300941532509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_199
      · exact prime_oneHundredFiftySevenEY_5190127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3300941532509) ^ 1650470766254 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3300941532509) ^ 194173031324 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3300941532509) ^ 70232798564 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3300941532509) ^ 16587645892 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3300941532509) ^ 636004 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3445936283891 : Nat.Prime 3445936283891 := by
  apply lucas_primality 3445936283891 (6 : ZMod 3445936283891)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (45697, 1), (7540837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (45697, 1), (7540837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3445936283891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_45697
      · exact prime_oneHundredFiftySevenEY_7540837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3445936283891) ^ 1722968141945 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3445936283891) ^ 689187256778 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3445936283891) ^ 75408370 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3445936283891) ^ 456970 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4052761929793 : Nat.Prime 4052761929793 := by
  apply lucas_primality 4052761929793 (5 : ZMod 4052761929793)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (17, 1), (137961667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (17, 1), (137961667, 1)] : List FactorBlock).map factorBlockValue).prod) = 4052761929793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_137961667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4052761929793) ^ 2026380964896 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4052761929793) ^ 1350920643264 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4052761929793) ^ 238397760576 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4052761929793) ^ 29376 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4500610324117 : Nat.Prime 4500610324117 := by
  apply lucas_primality 4500610324117 (2 : ZMod 4500610324117)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (10136509739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (10136509739, 1)] : List FactorBlock).map factorBlockValue).prod) = 4500610324117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_10136509739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4500610324117) ^ 2250305162058 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4500610324117) ^ 1500203441372 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4500610324117) ^ 121638116868 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4500610324117) ^ 444 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4692397198843 : Nat.Prime 4692397198843 := by
  apply lucas_primality 4692397198843 (5 : ZMod 4692397198843)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (919, 1), (7213, 1), (13109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (919, 1), (7213, 1), (13109, 1)] : List FactorBlock).map factorBlockValue).prod) = 4692397198843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_919
      · exact prime_oneHundredFiftySevenEY_7213
      · exact prime_oneHundredFiftySevenEY_13109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4692397198843) ^ 2346198599421 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4692397198843) ^ 1564132399614 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4692397198843) ^ 5105981718 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4692397198843) ^ 650547234 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4692397198843) ^ 357952338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4732560251773 : Nat.Prime 4732560251773 := by
  apply lucas_primality 4732560251773 (2 : ZMod 4732560251773)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2053, 1), (2441, 1), (78697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2053, 1), (2441, 1), (78697, 1)] : List FactorBlock).map factorBlockValue).prod) = 4732560251773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_2053
      · exact prime_oneHundredFiftySevenEY_2441
      · exact prime_oneHundredFiftySevenEY_78697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4732560251773) ^ 2366280125886 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4732560251773) ^ 1577520083924 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4732560251773) ^ 2305192524 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4732560251773) ^ 1938779292 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4732560251773) ^ 60136476 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_5463908494817 : Nat.Prime 5463908494817 := by
  apply lucas_primality 5463908494817 (3 : ZMod 5463908494817)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (31, 1), (323998369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (31, 1), (323998369, 1)] : List FactorBlock).map factorBlockValue).prod) = 5463908494817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_323998369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5463908494817) ^ 2731954247408 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5463908494817) ^ 321406382048 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5463908494817) ^ 176255112736 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5463908494817) ^ 16864 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_6251931883559 : Nat.Prime 6251931883559 := by
  apply lucas_primality 6251931883559 (13 : ZMod 6251931883559)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3125965941779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3125965941779, 1)] : List FactorBlock).map factorBlockValue).prod) = 6251931883559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3125965941779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 6251931883559) ^ 3125965941779 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 6251931883559) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_8018274392501 : Nat.Prime 8018274392501 := by
  apply lucas_primality 8018274392501 (2 : ZMod 8018274392501)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (43, 1), (74588599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (43, 1), (74588599, 1)] : List FactorBlock).map factorBlockValue).prod) = 8018274392501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_74588599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8018274392501) ^ 4009137196250 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8018274392501) ^ 1603654878500 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8018274392501) ^ 186471497500 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8018274392501) ^ 107500 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_11340844139477 : Nat.Prime 11340844139477 := by
  apply lucas_primality 11340844139477 (2 : ZMod 11340844139477)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (271, 1), (69284989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (271, 1), (69284989, 1)] : List FactorBlock).map factorBlockValue).prod) = 11340844139477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_151
      · exact prime_oneHundredFiftySevenEY_271
      · exact prime_oneHundredFiftySevenEY_69284989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11340844139477) ^ 5670422069738 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11340844139477) ^ 75104928076 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11340844139477) ^ 41848133356 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11340844139477) ^ 163684 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_12503863767119 : Nat.Prime 12503863767119 := by
  apply lucas_primality 12503863767119 (7 : ZMod 12503863767119)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6251931883559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6251931883559, 1)] : List FactorBlock).map factorBlockValue).prod) = 12503863767119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_6251931883559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 12503863767119) ^ 6251931883559 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 12503863767119) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_16311725373859 : Nat.Prime 16311725373859 := by
  apply lucas_primality 16311725373859 (2 : ZMod 16311725373859)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (3489885617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (3489885617, 1)] : List FactorBlock).map factorBlockValue).prod) = 16311725373859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_3489885617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16311725373859) ^ 8155862686929 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16311725373859) ^ 5437241791286 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16311725373859) ^ 858511861782 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16311725373859) ^ 397846960338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16311725373859) ^ 4674 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_17500951257067 : Nat.Prime 17500951257067 := by
  apply lucas_primality 17500951257067 (2 : ZMod 17500951257067)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (972275069837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (972275069837, 1)] : List FactorBlock).map factorBlockValue).prod) = 17500951257067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_972275069837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17500951257067) ^ 8750475628533 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17500951257067) ^ 5833650419022 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17500951257067) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_18317613513707 : Nat.Prime 18317613513707 := by
  apply lucas_primality 18317613513707 (2 : ZMod 18317613513707)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (37080189299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (37080189299, 1)] : List FactorBlock).map factorBlockValue).prod) = 18317613513707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_37080189299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18317613513707) ^ 9158806756853 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18317613513707) ^ 1409047193362 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18317613513707) ^ 964084921774 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18317613513707) ^ 494 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_18646755818689 : Nat.Prime 18646755818689 := by
  apply lucas_primality 18646755818689 (7 : ZMod 18646755818689)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (23, 1), (47, 1), (311, 1), (96293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (23, 1), (47, 1), (311, 1), (96293, 1)] : List FactorBlock).map factorBlockValue).prod) = 18646755818689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_311
      · exact prime_oneHundredFiftySevenEY_96293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18646755818689) ^ 9323377909344 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 18646755818689) ^ 6215585272896 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 18646755818689) ^ 810728513856 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 18646755818689) ^ 396739485504 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 18646755818689) ^ 59957414208 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 18646755818689) ^ 193646016 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_19982281804183 : Nat.Prime 19982281804183 := by
  apply lucas_primality 19982281804183 (3 : ZMod 19982281804183)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131, 1), (2824750043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131, 1), (2824750043, 1)] : List FactorBlock).map factorBlockValue).prod) = 19982281804183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_131
      · exact prime_oneHundredFiftySevenEY_2824750043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19982281804183) ^ 9991140902091 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19982281804183) ^ 6660760601394 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19982281804183) ^ 152536502322 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 19982281804183) ^ 7074 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_24316571578759 : Nat.Prime 24316571578759 := by
  apply lucas_primality 24316571578759 (6 : ZMod 24316571578759)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4052761929793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4052761929793, 1)] : List FactorBlock).map factorBlockValue).prod) = 24316571578759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_4052761929793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 24316571578759) ^ 12158285789379 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24316571578759) ^ 8105523859586 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 24316571578759) ^ 6 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_39223905608287 : Nat.Prime 39223905608287 := by
  apply lucas_primality 39223905608287 (3 : ZMod 39223905608287)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (311300838161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (311300838161, 1)] : List FactorBlock).map factorBlockValue).prod) = 39223905608287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_311300838161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39223905608287) ^ 19611952804143 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39223905608287) ^ 13074635202762 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39223905608287) ^ 5603415086898 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 39223905608287) ^ 126 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_39812972784661 : Nat.Prime 39812972784661 := by
  apply lucas_primality 39812972784661 (2 : ZMod 39812972784661)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (73727727379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (73727727379, 1)] : List FactorBlock).map factorBlockValue).prod) = 39812972784661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_73727727379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39812972784661) ^ 19906486392330 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39812972784661) ^ 13270990928220 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39812972784661) ^ 7962594556932 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 39812972784661) ^ 540 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_44489649271439 : Nat.Prime 44489649271439 := by
  apply lucas_primality 44489649271439 (11 : ZMod 44489649271439)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (220747, 1), (464381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (220747, 1), (464381, 1)] : List FactorBlock).map factorBlockValue).prod) = 44489649271439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_220747
      · exact prime_oneHundredFiftySevenEY_464381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 44489649271439) ^ 22244824635719 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 44489649271439) ^ 6355664181634 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 44489649271439) ^ 1435149976498 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 44489649271439) ^ 201541354 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 44489649271439) ^ 95804198 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_46719282182381 : Nat.Prime 46719282182381 := by
  apply lucas_primality 46719282182381 (2 : ZMod 46719282182381)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (67, 1), (83, 1), (420061879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (67, 1), (83, 1), (420061879, 1)] : List FactorBlock).map factorBlockValue).prod) = 46719282182381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_67
      · exact prime_oneHundredFiftySevenEY_83
      · exact prime_oneHundredFiftySevenEY_420061879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46719282182381) ^ 23359641091190 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 46719282182381) ^ 9343856436476 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 46719282182381) ^ 697302719140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 46719282182381) ^ 562882917860 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 46719282182381) ^ 111220 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_47411856152519 : Nat.Prime 47411856152519 := by
  apply lucas_primality 47411856152519 (11 : ZMod 47411856152519)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (17, 1), (227, 1), (1231, 1), (34897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (17, 1), (227, 1), (1231, 1), (34897, 1)] : List FactorBlock).map factorBlockValue).prod) = 47411856152519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_227
      · exact prime_oneHundredFiftySevenEY_1231
      · exact prime_oneHundredFiftySevenEY_34897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47411856152519) ^ 23705928076259 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 4310168741138 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 3647065857886 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 2788932714854 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 208862802434 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 38514911578 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 47411856152519) ^ 1358622694 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_57416501568149 : Nat.Prime 57416501568149 := by
  apply lucas_primality 57416501568149 (2 : ZMod 57416501568149)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (181, 1), (1300074757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (181, 1), (1300074757, 1)] : List FactorBlock).map factorBlockValue).prod) = 57416501568149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_181
      · exact prime_oneHundredFiftySevenEY_1300074757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57416501568149) ^ 28708250784074 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57416501568149) ^ 941254124068 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57416501568149) ^ 317218240708 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 57416501568149) ^ 44164 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_65246901495437 : Nat.Prime 65246901495437 := by
  apply lucas_primality 65246901495437 (2 : ZMod 65246901495437)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16311725373859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16311725373859, 1)] : List FactorBlock).map factorBlockValue).prod) = 65246901495437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_16311725373859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 65246901495437) ^ 32623450747718 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 65246901495437) ^ 4 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_73881619525759 : Nat.Prime 73881619525759 := by
  apply lucas_primality 73881619525759 (6 : ZMod 73881619525759)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (36110273473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (36110273473, 1)] : List FactorBlock).map factorBlockValue).prod) = 73881619525759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_36110273473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73881619525759) ^ 36940809762879 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 73881619525759) ^ 24627206508586 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 73881619525759) ^ 6716510865978 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 73881619525759) ^ 2383278049218 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 73881619525759) ^ 2046 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_105393208617659 : Nat.Prime 105393208617659 := by
  apply lucas_primality 105393208617659 (2 : ZMod 105393208617659)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (18869, 1), (214827757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (18869, 1), (214827757, 1)] : List FactorBlock).map factorBlockValue).prod) = 105393208617659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_18869
      · exact prime_oneHundredFiftySevenEY_214827757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105393208617659) ^ 52696604308829 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105393208617659) ^ 8107169893666 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105393208617659) ^ 5585521682 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 105393208617659) ^ 490594 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_109753939517351 : Nat.Prime 109753939517351 := by
  apply lucas_primality 109753939517351 (29 : ZMod 109753939517351)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (97, 1), (1879, 1), (388499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (97, 1), (1879, 1), (388499, 1)] : List FactorBlock).map factorBlockValue).prod) = 109753939517351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_97
      · exact prime_oneHundredFiftySevenEY_1879
      · exact prime_oneHundredFiftySevenEY_388499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 109753939517351) ^ 54876969758675 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 109753939517351) ^ 21950787903470 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 109753939517351) ^ 3540449661850 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 109753939517351) ^ 1131483912550 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 109753939517351) ^ 58410824650 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (29 : ZMod 109753939517351) ^ 282507650 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_125506879294751 : Nat.Prime 125506879294751 := by
  apply lucas_primality 125506879294751 (11 : ZMod 125506879294751)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (179, 1), (2804623001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (179, 1), (2804623001, 1)] : List FactorBlock).map factorBlockValue).prod) = 125506879294751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_179
      · exact prime_oneHundredFiftySevenEY_2804623001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 125506879294751) ^ 62753439647375 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 125506879294751) ^ 25101375858950 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 125506879294751) ^ 701155750250 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 125506879294751) ^ 44750 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_166225866747419 : Nat.Prime 166225866747419 := by
  apply lucas_primality 166225866747419 (2 : ZMod 166225866747419)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (1768360284547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (1768360284547, 1)] : List FactorBlock).map factorBlockValue).prod) = 166225866747419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_47
      · exact prime_oneHundredFiftySevenEY_1768360284547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 166225866747419) ^ 83112933373709 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 166225866747419) ^ 3536720569094 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 166225866747419) ^ 94 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_216635296222567 : Nat.Prime 216635296222567 := by
  apply lucas_primality 216635296222567 (5 : ZMod 216635296222567)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (925791864199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (925791864199, 1)] : List FactorBlock).map factorBlockValue).prod) = 216635296222567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_925791864199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 216635296222567) ^ 108317648111283 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216635296222567) ^ 72211765407522 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216635296222567) ^ 16664253555582 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 216635296222567) ^ 234 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_294861947626403 : Nat.Prime 294861947626403 := by
  apply lucas_primality 294861947626403 (2 : ZMod 294861947626403)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (11340844139477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (11340844139477, 1)] : List FactorBlock).map factorBlockValue).prod) = 294861947626403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_11340844139477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 294861947626403) ^ 147430973813201 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294861947626403) ^ 22681688278954 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 294861947626403) ^ 26 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_296630166648581 : Nat.Prime 296630166648581 := by
  apply lucas_primality 296630166648581 (2 : ZMod 296630166648581)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (41, 1), (97, 1), (120300667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (41, 1), (97, 1), (120300667, 1)] : List FactorBlock).map factorBlockValue).prod) = 296630166648581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_97
      · exact prime_oneHundredFiftySevenEY_120300667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 296630166648581) ^ 148315083324290 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 296630166648581) ^ 59326033329716 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 296630166648581) ^ 9568715053180 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 296630166648581) ^ 7234882113380 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 296630166648581) ^ 3058042955140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 296630166648581) ^ 2465740 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_299311370204641 : Nat.Prime 299311370204641 := by
  apply lucas_primality 299311370204641 (13 : ZMod 299311370204641)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (167, 1), (3733924279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (167, 1), (3733924279, 1)] : List FactorBlock).map factorBlockValue).prod) = 299311370204641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_167
      · exact prime_oneHundredFiftySevenEY_3733924279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 299311370204641) ^ 149655685102320 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 299311370204641) ^ 99770456734880 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 299311370204641) ^ 59862274040928 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 299311370204641) ^ 1792283653920 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 299311370204641) ^ 80160 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_414763615828967 : Nat.Prime 414763615828967 := by
  apply lucas_primality 414763615828967 (5 : ZMod 414763615828967)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (52517, 1), (96313439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (52517, 1), (96313439, 1)] : List FactorBlock).map factorBlockValue).prod) = 414763615828967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_52517
      · exact prime_oneHundredFiftySevenEY_96313439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 414763615828967) ^ 207381807914483 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 414763615828967) ^ 10116185751926 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 414763615828967) ^ 7897701998 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 414763615828967) ^ 4306394 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_440087853767459 : Nat.Prime 440087853767459 := by
  apply lucas_primality 440087853767459 (2 : ZMod 440087853767459)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (71, 1), (881, 1), (6293081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (71, 1), (881, 1), (6293081, 1)] : List FactorBlock).map factorBlockValue).prod) = 440087853767459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_71
      · exact prime_oneHundredFiftySevenEY_881
      · exact prime_oneHundredFiftySevenEY_6293081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440087853767459) ^ 220043926883729 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 440087853767459) ^ 33852911828266 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 440087853767459) ^ 10234601250406 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 440087853767459) ^ 6198420475598 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 440087853767459) ^ 499532183618 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 440087853767459) ^ 69932018 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_447522139648537 : Nat.Prime 447522139648537 := by
  apply lucas_primality 447522139648537 (5 : ZMod 447522139648537)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (18646755818689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (18646755818689, 1)] : List FactorBlock).map factorBlockValue).prod) = 447522139648537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_18646755818689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 447522139648537) ^ 223761069824268 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 447522139648537) ^ 149174046549512 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 447522139648537) ^ 24 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_473978758418567 : Nat.Prime 473978758418567 := by
  apply lucas_primality 473978758418567 (5 : ZMod 473978758418567)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2365471, 1), (100186973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2365471, 1), (100186973, 1)] : List FactorBlock).map factorBlockValue).prod) = 473978758418567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_2365471
      · exact prime_oneHundredFiftySevenEY_100186973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 473978758418567) ^ 236989379209283 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 473978758418567) ^ 200373946 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 473978758418567) ^ 4730942 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_681168754045183 : Nat.Prime 681168754045183 := by
  apply lucas_primality 681168754045183 (3 : ZMod 681168754045183)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (123553, 1), (70681673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (123553, 1), (70681673, 1)] : List FactorBlock).map factorBlockValue).prod) = 681168754045183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_123553
      · exact prime_oneHundredFiftySevenEY_70681673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 681168754045183) ^ 340584377022591 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 681168754045183) ^ 227056251348394 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 681168754045183) ^ 52397596465014 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 681168754045183) ^ 5513170494 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 681168754045183) ^ 9637134 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_823465483808503 : Nat.Prime 823465483808503 := by
  apply lucas_primality 823465483808503 (3 : ZMod 823465483808503)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (4732560251773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (4732560251773, 1)] : List FactorBlock).map factorBlockValue).prod) = 823465483808503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_4732560251773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 823465483808503) ^ 411732741904251 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 823465483808503) ^ 274488494602834 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 823465483808503) ^ 28395361510638 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 823465483808503) ^ 174 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_856812828014161 : Nat.Prime 856812828014161 := by
  apply lucas_primality 856812828014161 (13 : ZMod 856812828014161)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (137, 1), (6553, 1), (3976619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (137, 1), (6553, 1), (3976619, 1)] : List FactorBlock).map factorBlockValue).prod) = 856812828014161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_137
      · exact prime_oneHundredFiftySevenEY_6553
      · exact prime_oneHundredFiftySevenEY_3976619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 856812828014161) ^ 428406414007080 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 856812828014161) ^ 285604276004720 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 856812828014161) ^ 171362565602832 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 856812828014161) ^ 6254108233680 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 856812828014161) ^ 130751232720 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 856812828014161) ^ 215462640 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_911564969677267 : Nat.Prime 911564969677267 := by
  apply lucas_primality 911564969677267 (2 : ZMod 911564969677267)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (641, 1), (691, 1), (4698697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (641, 1), (691, 1), (4698697, 1)] : List FactorBlock).map factorBlockValue).prod) = 911564969677267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_73
      · exact prime_oneHundredFiftySevenEY_641
      · exact prime_oneHundredFiftySevenEY_691
      · exact prime_oneHundredFiftySevenEY_4698697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 911564969677267) ^ 455782484838633 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 911564969677267) ^ 303854989892422 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 911564969677267) ^ 12487191365442 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 911564969677267) ^ 1422098236626 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 911564969677267) ^ 1319196772326 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 911564969677267) ^ 194003778 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_923323789619719 : Nat.Prime 923323789619719 := by
  apply lucas_primality 923323789619719 (11 : ZMod 923323789619719)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1709, 1), (2094075119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1709, 1), (2094075119, 1)] : List FactorBlock).map factorBlockValue).prod) = 923323789619719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_1709
      · exact prime_oneHundredFiftySevenEY_2094075119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 923323789619719) ^ 461661894809859 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 923323789619719) ^ 307774596539906 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 923323789619719) ^ 21472646270226 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 923323789619719) ^ 540271380702 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 923323789619719) ^ 440922 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_993835141855931 : Nat.Prime 993835141855931 := by
  apply lucas_primality 993835141855931 (2 : ZMod 993835141855931)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (239, 1), (37802782117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (239, 1), (37802782117, 1)] : List FactorBlock).map factorBlockValue).prod) = 993835141855931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_239
      · exact prime_oneHundredFiftySevenEY_37802782117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 993835141855931) ^ 496917570927965 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 993835141855931) ^ 198767028371186 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 993835141855931) ^ 90348649259630 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 993835141855931) ^ 4158306032870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 993835141855931) ^ 26290 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1502334828756173 : Nat.Prime 1502334828756173 := by
  apply lucas_primality 1502334828756173 (2 : ZMod 1502334828756173)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (59, 1), (155264037697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (59, 1), (155264037697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1502334828756173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_155264037697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1502334828756173) ^ 751167414378086 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502334828756173) ^ 36642312896492 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502334828756173) ^ 25463302182308 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502334828756173) ^ 9676 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1587852908632427 : Nat.Prime 1587852908632427 := by
  apply lucas_primality 1587852908632427 (2 : ZMod 1587852908632427)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27361549, 1), (29016137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27361549, 1), (29016137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1587852908632427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_27361549
      · exact prime_oneHundredFiftySevenEY_29016137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1587852908632427) ^ 793926454316213 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1587852908632427) ^ 58032274 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1587852908632427) ^ 54723098 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1798731561437357 : Nat.Prime 1798731561437357 := by
  apply lucas_primality 1798731561437357 (2 : ZMod 1798731561437357)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (307, 1), (2287, 1), (7038181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (307, 1), (2287, 1), (7038181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1798731561437357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_307
      · exact prime_oneHundredFiftySevenEY_2287
      · exact prime_oneHundredFiftySevenEY_7038181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1798731561437357) ^ 899365780718678 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1798731561437357) ^ 256961651633908 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1798731561437357) ^ 138363966264412 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1798731561437357) ^ 5859060460708 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1798731561437357) ^ 786502650388 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1798731561437357) ^ 255567676 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1897077755117863 : Nat.Prime 1897077755117863 := by
  apply lucas_primality 1897077755117863 (3 : ZMod 1897077755117863)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (105393208617659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (105393208617659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1897077755117863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_105393208617659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1897077755117863) ^ 948538877558931 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1897077755117863) ^ 632359251705954 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1897077755117863) ^ 18 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2086057137376703 : Nat.Prime 2086057137376703 := by
  apply lucas_primality 2086057137376703 (5 : ZMod 2086057137376703)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (179, 1), (13646312047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (179, 1), (13646312047, 1)] : List FactorBlock).map factorBlockValue).prod) = 2086057137376703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_179
      · exact prime_oneHundredFiftySevenEY_13646312047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2086057137376703) ^ 1043028568688351 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2086057137376703) ^ 298008162482386 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2086057137376703) ^ 34197657989782 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2086057137376703) ^ 11653950488138 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2086057137376703) ^ 152866 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3322357473707177 : Nat.Prime 3322357473707177 := by
  apply lucas_primality 3322357473707177 (3 : ZMod 3322357473707177)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (241, 1), (1723214457317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (241, 1), (1723214457317, 1)] : List FactorBlock).map factorBlockValue).prod) = 3322357473707177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_241
      · exact prime_oneHundredFiftySevenEY_1723214457317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3322357473707177) ^ 1661178736853588 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3322357473707177) ^ 13785715658536 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3322357473707177) ^ 1928 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3646259878709069 : Nat.Prime 3646259878709069 := by
  apply lucas_primality 3646259878709069 (2 : ZMod 3646259878709069)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (911564969677267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (911564969677267, 1)] : List FactorBlock).map factorBlockValue).prod) = 3646259878709069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_911564969677267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3646259878709069) ^ 1823129939354534 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3646259878709069) ^ 4 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7422341776157669 : Nat.Prime 7422341776157669 := by
  apply lucas_primality 7422341776157669 (2 : ZMod 7422341776157669)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1069, 1), (15401, 1), (2748973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1069, 1), (15401, 1), (2748973, 1)] : List FactorBlock).map factorBlockValue).prod) = 7422341776157669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_1069
      · exact prime_oneHundredFiftySevenEY_15401
      · exact prime_oneHundredFiftySevenEY_2748973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7422341776157669) ^ 3711170888078834 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7422341776157669) ^ 181032726247748 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7422341776157669) ^ 6943257040372 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7422341776157669) ^ 481938950468 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7422341776157669) ^ 2700041716 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_7438146770479819 : Nat.Prime 7438146770479819 := by
  apply lucas_primality 7438146770479819 (2 : ZMod 7438146770479819)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (65246901495437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (65246901495437, 1)] : List FactorBlock).map factorBlockValue).prod) = 7438146770479819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_65246901495437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7438146770479819) ^ 3719073385239909 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438146770479819) ^ 2479382256826606 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438146770479819) ^ 391481408972622 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438146770479819) ^ 114 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_13737029566662823 : Nat.Prime 13737029566662823 := by
  apply lucas_primality 13737029566662823 (3 : ZMod 13737029566662823)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (251033, 1), (1302904927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (251033, 1), (1302904927, 1)] : List FactorBlock).map factorBlockValue).prod) = 13737029566662823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_251033
      · exact prime_oneHundredFiftySevenEY_1302904927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13737029566662823) ^ 6868514783331411 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737029566662823) ^ 4579009855554274 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737029566662823) ^ 1962432795237546 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737029566662823) ^ 54722006934 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 13737029566662823) ^ 10543386 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_15004817837488049 : Nat.Prime 15004817837488049 := by
  apply lucas_primality 15004817837488049 (3 : ZMod 15004817837488049)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (92671, 1), (10119682693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (92671, 1), (10119682693, 1)] : List FactorBlock).map factorBlockValue).prod) = 15004817837488049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_92671
      · exact prime_oneHundredFiftySevenEY_10119682693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15004817837488049) ^ 7502408918744024 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15004817837488049) ^ 161914923088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15004817837488049) ^ 1482736 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_25852459481259721 : Nat.Prime 25852459481259721 := by
  apply lucas_primality 25852459481259721 (11 : ZMod 25852459481259721)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (103, 1), (211, 1), (9912904907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (103, 1), (211, 1), (9912904907, 1)] : List FactorBlock).map factorBlockValue).prod) = 25852459481259721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_103
      · exact prime_oneHundredFiftySevenEY_211
      · exact prime_oneHundredFiftySevenEY_9912904907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 25852459481259721) ^ 12926229740629860 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 25852459481259721) ^ 8617486493753240 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 25852459481259721) ^ 5170491896251944 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 25852459481259721) ^ 250994752245240 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 25852459481259721) ^ 122523504650520 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 25852459481259721) ^ 2607960 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_42658088257671031 : Nat.Prime 42658088257671031 := by
  apply lucas_primality 42658088257671031 (3 : ZMod 42658088257671031)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (473978758418567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (473978758418567, 1)] : List FactorBlock).map factorBlockValue).prod) = 42658088257671031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_473978758418567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42658088257671031) ^ 21329044128835515 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 42658088257671031) ^ 14219362752557010 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 42658088257671031) ^ 8531617651534206 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 42658088257671031) ^ 90 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_107214956384313287 : Nat.Prime 107214956384313287 := by
  apply lucas_primality 107214956384313287 (5 : ZMod 107214956384313287)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (349, 1), (637357217327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (349, 1), (637357217327, 1)] : List FactorBlock).map factorBlockValue).prod) = 107214956384313287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_241
      · exact prime_oneHundredFiftySevenEY_349
      · exact prime_oneHundredFiftySevenEY_637357217327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 107214956384313287) ^ 53607478192156643 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 107214956384313287) ^ 444875337694246 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 107214956384313287) ^ 307206178751614 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 107214956384313287) ^ 168218 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_114852055383311273 : Nat.Prime 114852055383311273 := by
  apply lucas_primality 114852055383311273 (3 : ZMod 114852055383311273)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (683, 1), (953, 1), (26029, 1), (65183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (683, 1), (953, 1), (26029, 1), (65183, 1)] : List FactorBlock).map factorBlockValue).prod) = 114852055383311273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_683
      · exact prime_oneHundredFiftySevenEY_953
      · exact prime_oneHundredFiftySevenEY_26029
      · exact prime_oneHundredFiftySevenEY_65183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 114852055383311273) ^ 57426027691655636 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114852055383311273) ^ 8834773491023944 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114852055383311273) ^ 168158207003384 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114852055383311273) ^ 120516322542824 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114852055383311273) ^ 4412465149768 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114852055383311273) ^ 1761994007384 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_126196125615518533 : Nat.Prime 126196125615518533 := by
  apply lucas_primality 126196125615518533 (5 : ZMod 126196125615518533)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1502334828756173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1502334828756173, 1)] : List FactorBlock).map factorBlockValue).prod) = 126196125615518533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_1502334828756173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 126196125615518533) ^ 63098062807759266 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 126196125615518533) ^ 42065375205172844 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 126196125615518533) ^ 18028017945074076 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 126196125615518533) ^ 84 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_126945641834432899 : Nat.Prime 126945641834432899 := by
  apply lucas_primality 126945641834432899 (7 : ZMod 126945641834432899)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (1223, 1), (72383934739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (1223, 1), (72383934739, 1)] : List FactorBlock).map factorBlockValue).prod) = 126945641834432899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_239
      · exact prime_oneHundredFiftySevenEY_1223
      · exact prime_oneHundredFiftySevenEY_72383934739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 126945641834432899) ^ 63472820917216449 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 126945641834432899) ^ 42315213944810966 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 126945641834432899) ^ 531153313114782 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 126945641834432899) ^ 103798562415726 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 126945641834432899) ^ 1753782 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_188358053082422677 : Nat.Prime 188358053082422677 := by
  apply lucas_primality 188358053082422677 (5 : ZMod 188358053082422677)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (923323789619719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (923323789619719, 1)] : List FactorBlock).map factorBlockValue).prod) = 188358053082422677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_923323789619719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 188358053082422677) ^ 94179026541211338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 188358053082422677) ^ 62786017694140892 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 188358053082422677) ^ 11079885475436628 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 188358053082422677) ^ 204 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_403507485887207099 : Nat.Prime 403507485887207099 := by
  apply lucas_primality 403507485887207099 (2 : ZMod 403507485887207099)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (337, 1), (397, 1), (8331488861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (337, 1), (397, 1), (8331488861, 1)] : List FactorBlock).map factorBlockValue).prod) = 403507485887207099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_181
      · exact prime_oneHundredFiftySevenEY_337
      · exact prime_oneHundredFiftySevenEY_397
      · exact prime_oneHundredFiftySevenEY_8331488861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 403507485887207099) ^ 201753742943603549 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 403507485887207099) ^ 2229323126448658 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 403507485887207099) ^ 1197351590169754 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 403507485887207099) ^ 1016391652108834 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 403507485887207099) ^ 48431618 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_800167674409054801 : Nat.Prime 800167674409054801 := by
  apply lucas_primality 800167674409054801 (7 : ZMod 800167674409054801)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (17, 1), (39223905608287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (17, 1), (39223905608287, 1)] : List FactorBlock).map factorBlockValue).prod) = 800167674409054801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_39223905608287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 800167674409054801) ^ 400083837204527400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 800167674409054801) ^ 266722558136351600 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 800167674409054801) ^ 160033534881810960 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 800167674409054801) ^ 47068686729944400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 800167674409054801) ^ 20400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_807014971774414199 : Nat.Prime 807014971774414199 := by
  apply lucas_primality 807014971774414199 (11 : ZMod 807014971774414199)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (403507485887207099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (403507485887207099, 1)] : List FactorBlock).map factorBlockValue).prod) = 807014971774414199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_403507485887207099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 807014971774414199) ^ 403507485887207099 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 807014971774414199) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1085329998216494351 : Nat.Prime 1085329998216494351 := by
  apply lucas_primality 1085329998216494351 (19 : ZMod 1085329998216494351)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 2), (59, 1), (1019137047013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 2), (59, 1), (1019137047013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085329998216494351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_19
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_1019137047013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1085329998216494351) ^ 542664999108247175 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1085329998216494351) ^ 217065999643298870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1085329998216494351) ^ 57122631485078650 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1085329998216494351) ^ 18395423698584650 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 1085329998216494351) ^ 1064950 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1118899774900828603 : Nat.Prime 1118899774900828603 := by
  apply lucas_primality 1118899774900828603 (5 : ZMod 1118899774900828603)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (15122951, 1), (373671049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (15122951, 1), (373671049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118899774900828603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_15122951
      · exact prime_oneHundredFiftySevenEY_373671049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1118899774900828603) ^ 559449887450414301 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1118899774900828603) ^ 372966591633609534 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1118899774900828603) ^ 101718161354620782 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1118899774900828603) ^ 73986867702 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1118899774900828603) ^ 2994344298 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1162664678671389767 : Nat.Prime 1162664678671389767 := by
  apply lucas_primality 1162664678671389767 (5 : ZMod 1162664678671389767)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (403679, 1), (1440085660477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (403679, 1), (1440085660477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162664678671389767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_403679
      · exact prime_oneHundredFiftySevenEY_1440085660477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1162664678671389767) ^ 581332339335694883 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1162664678671389767) ^ 2880171320954 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1162664678671389767) ^ 807358 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1181103527287959971 : Nat.Prime 1181103527287959971 := by
  apply lucas_primality 1181103527287959971 (2 : ZMod 1181103527287959971)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (347, 1), (43133, 1), (7891304947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (347, 1), (43133, 1), (7891304947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1181103527287959971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_347
      · exact prime_oneHundredFiftySevenEY_43133
      · exact prime_oneHundredFiftySevenEY_7891304947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1181103527287959971) ^ 590551763643979985 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1181103527287959971) ^ 236220705457591994 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1181103527287959971) ^ 3403756562789510 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1181103527287959971) ^ 27382828166090 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1181103527287959971) ^ 149671510 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1463030382204517463 : Nat.Prime 1463030382204517463 := by
  apply lucas_primality 1463030382204517463 (5 : ZMod 1463030382204517463)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13033, 1), (8018274392501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13033, 1), (8018274392501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1463030382204517463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13033
      · exact prime_oneHundredFiftySevenEY_8018274392501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1463030382204517463) ^ 731515191102258731 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1463030382204517463) ^ 209004340314931066 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1463030382204517463) ^ 112255841495014 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1463030382204517463) ^ 182462 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1505347852809833407 : Nat.Prime 1505347852809833407 := by
  apply lucas_primality 1505347852809833407 (5 : ZMod 1505347852809833407)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (137, 1), (211, 1), (87669271957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (137, 1), (211, 1), (87669271957, 1)] : List FactorBlock).map factorBlockValue).prod) = 1505347852809833407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_137
      · exact prime_oneHundredFiftySevenEY_211
      · exact prime_oneHundredFiftySevenEY_87669271957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1505347852809833407) ^ 752673926404916703 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1505347852809833407) ^ 501782617603277802 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1505347852809833407) ^ 136849804800893946 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1505347852809833407) ^ 10987940531458638 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1505347852809833407) ^ 7134350013316746 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1505347852809833407) ^ 17170758 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2170659996432988703 : Nat.Prime 2170659996432988703 := by
  apply lucas_primality 2170659996432988703 (5 : ZMod 2170659996432988703)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1085329998216494351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1085329998216494351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2170659996432988703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_1085329998216494351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2170659996432988703) ^ 1085329998216494351 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2170659996432988703) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2776685510969483177 : Nat.Prime 2776685510969483177 := by
  apply lucas_primality 2776685510969483177 (5 : ZMod 2776685510969483177)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (367, 1), (57587, 1), (75680929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (367, 1), (57587, 1), (75680929, 1)] : List FactorBlock).map factorBlockValue).prod) = 2776685510969483177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_367
      · exact prime_oneHundredFiftySevenEY_57587
      · exact prime_oneHundredFiftySevenEY_75680929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2776685510969483177) ^ 1388342755484741588 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2776685510969483177) ^ 396669358709926168 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2776685510969483177) ^ 89570500353854296 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2776685510969483177) ^ 7565900574848728 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2776685510969483177) ^ 48217228037048 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2776685510969483177) ^ 36689368744 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3338222149673586311 : Nat.Prime 3338222149673586311 := by
  apply lucas_primality 3338222149673586311 (11 : ZMod 3338222149673586311)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (199, 1), (2543, 2), (11278247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (199, 1), (2543, 2), (11278247, 1)] : List FactorBlock).map factorBlockValue).prod) = 3338222149673586311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_199
      · exact prime_oneHundredFiftySevenEY_2543
      · exact prime_oneHundredFiftySevenEY_11278247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3338222149673586311) ^ 1669111074836793155 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3338222149673586311) ^ 667644429934717262 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3338222149673586311) ^ 145140093464068970 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3338222149673586311) ^ 16774985676751690 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3338222149673586311) ^ 1312710243678170 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3338222149673586311) ^ 295987678730 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3387476581164248711 : Nat.Prime 3387476581164248711 := by
  apply lucas_primality 3387476581164248711 (13 : ZMod 3387476581164248711)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (137, 1), (30011, 1), (2009515733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (137, 1), (30011, 1), (2009515733, 1)] : List FactorBlock).map factorBlockValue).prod) = 3387476581164248711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_137
      · exact prime_oneHundredFiftySevenEY_30011
      · exact prime_oneHundredFiftySevenEY_2009515733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3387476581164248711) ^ 1693738290582124355 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 3387476581164248711) ^ 677495316232849742 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 3387476581164248711) ^ 82621380028396310 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 3387476581164248711) ^ 24726106431855830 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 3387476581164248711) ^ 112874498722610 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 3387476581164248711) ^ 1685717870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_5798479076523484859 : Nat.Prime 5798479076523484859 := by
  apply lucas_primality 5798479076523484859 (6 : ZMod 5798479076523484859)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (571, 1), (12185273, 1), (32053051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (571, 1), (12185273, 1), (32053051, 1)] : List FactorBlock).map factorBlockValue).prod) = 5798479076523484859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_571
      · exact prime_oneHundredFiftySevenEY_12185273
      · exact prime_oneHundredFiftySevenEY_32053051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5798479076523484859) ^ 2899239538261742429 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5798479076523484859) ^ 446036852040268066 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5798479076523484859) ^ 10154954599865998 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5798479076523484859) ^ 475859595146 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5798479076523484859) ^ 180902562958 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_10632652582618432337 : Nat.Prime 10632652582618432337 := by
  apply lucas_primality 10632652582618432337 (3 : ZMod 10632652582618432337)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (109, 1), (347621, 1), (17538366389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (109, 1), (347621, 1), (17538366389, 1)] : List FactorBlock).map factorBlockValue).prod) = 10632652582618432337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_109
      · exact prime_oneHundredFiftySevenEY_347621
      · exact prime_oneHundredFiftySevenEY_17538366389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10632652582618432337) ^ 5316326291309216168 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10632652582618432337) ^ 97547271400169104 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10632652582618432337) ^ 30586910982416 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10632652582618432337) ^ 606251024 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_11429954795135383141 : Nat.Prime 11429954795135383141 := by
  apply lucas_primality 11429954795135383141 (2 : ZMod 11429954795135383141)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (97, 1), (1019, 1), (1229, 1), (1568178377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (97, 1), (1019, 1), (1229, 1), (1568178377, 1)] : List FactorBlock).map factorBlockValue).prod) = 11429954795135383141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_97
      · exact prime_oneHundredFiftySevenEY_1019
      · exact prime_oneHundredFiftySevenEY_1229
      · exact prime_oneHundredFiftySevenEY_1568178377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11429954795135383141) ^ 5714977397567691570 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 3809984931711794380 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 2285990959027076628 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 117834585516859620 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 11216834931438060 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 9300207319068660 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11429954795135383141) ^ 7288682820 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_22213484087755865417 : Nat.Prime 22213484087755865417 := by
  apply lucas_primality 22213484087755865417 (3 : ZMod 22213484087755865417)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2776685510969483177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2776685510969483177, 1)] : List FactorBlock).map factorBlockValue).prod) = 22213484087755865417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_2776685510969483177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22213484087755865417) ^ 11106742043877932708 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 22213484087755865417) ^ 8 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_22715302610793335941 : Nat.Prime 22715302610793335941 := by
  apply lucas_primality 22715302610793335941 (2 : ZMod 22715302610793335941)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (126196125615518533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (126196125615518533, 1)] : List FactorBlock).map factorBlockValue).prod) = 22715302610793335941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_126196125615518533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22715302610793335941) ^ 11357651305396667970 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22715302610793335941) ^ 7571767536931111980 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22715302610793335941) ^ 4543060522158667188 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22715302610793335941) ^ 180 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_27114500385628308511 : Nat.Prime 27114500385628308511 := by
  apply lucas_primality 27114500385628308511 (6 : ZMod 27114500385628308511)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (2837, 1), (2227845033587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (2837, 1), (2227845033587, 1)] : List FactorBlock).map factorBlockValue).prod) = 27114500385628308511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_2837
      · exact prime_oneHundredFiftySevenEY_2227845033587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27114500385628308511) ^ 13557250192814154255 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 9038166795209436170 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 5422900077125661702 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 2464954580511664410 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 2085730798894485270 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 9557455194088230 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (6 : ZMod 27114500385628308511) ^ 12170730 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_40234053713351191217 : Nat.Prime 40234053713351191217 := by
  apply lucas_primality 40234053713351191217 (3 : ZMod 40234053713351191217)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61861, 1), (943079, 1), (43103129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61861, 1), (943079, 1), (43103129, 1)] : List FactorBlock).map factorBlockValue).prod) = 40234053713351191217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_61861
      · exact prime_oneHundredFiftySevenEY_943079
      · exact prime_oneHundredFiftySevenEY_43103129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40234053713351191217) ^ 20117026856675595608 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40234053713351191217) ^ 650394492707056 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40234053713351191217) ^ 42662442609104 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40234053713351191217) ^ 933436960304 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_44109767997717924059 : Nat.Prime 44109767997717924059 := by
  apply lucas_primality 44109767997717924059 (2 : ZMod 44109767997717924059)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (12391, 1), (57416501568149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (12391, 1), (57416501568149, 1)] : List FactorBlock).map factorBlockValue).prod) = 44109767997717924059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_12391
      · exact prime_oneHundredFiftySevenEY_57416501568149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44109767997717924059) ^ 22054883998858962029 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44109767997717924059) ^ 1422895741861868518 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44109767997717924059) ^ 3559823097225238 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44109767997717924059) ^ 768242 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_47672811646421489029 : Nat.Prime 47672811646421489029 := by
  apply lucas_primality 47672811646421489029 (2 : ZMod 47672811646421489029)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29537423, 1), (44832779351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29537423, 1), (44832779351, 1)] : List FactorBlock).map factorBlockValue).prod) = 47672811646421489029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_29537423
      · exact prime_oneHundredFiftySevenEY_44832779351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47672811646421489029) ^ 23836405823210744514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47672811646421489029) ^ 15890937215473829676 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47672811646421489029) ^ 1613980056636 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47672811646421489029) ^ 1063347228 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_86243986962245050681 : Nat.Prime 86243986962245050681 := by
  apply lucas_primality 86243986962245050681 (11 : ZMod 86243986962245050681)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (13875593, 1), (7399425239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (13875593, 1), (7399425239, 1)] : List FactorBlock).map factorBlockValue).prod) = 86243986962245050681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_13875593
      · exact prime_oneHundredFiftySevenEY_7399425239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 86243986962245050681) ^ 43121993481122525340 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 86243986962245050681) ^ 28747995654081683560 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 86243986962245050681) ^ 17248797392449010136 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 86243986962245050681) ^ 12320569566035007240 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 86243986962245050681) ^ 6215517200760 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 86243986962245050681) ^ 11655498120 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_105338187518725257337 : Nat.Prime 105338187518725257337 := by
  apply lucas_primality 105338187518725257337 (10 : ZMod 105338187518725257337)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1463030382204517463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1463030382204517463, 1)] : List FactorBlock).map factorBlockValue).prod) = 105338187518725257337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_1463030382204517463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 105338187518725257337) ^ 52669093759362628668 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 105338187518725257337) ^ 35112729172908419112 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 105338187518725257337) ^ 72 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_170128975289207860283 : Nat.Prime 170128975289207860283 := by
  apply lucas_primality 170128975289207860283 (5 : ZMod 170128975289207860283)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (663409, 1), (18317613513707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (663409, 1), (18317613513707, 1)] : List FactorBlock).map factorBlockValue).prod) = 170128975289207860283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_663409
      · exact prime_oneHundredFiftySevenEY_18317613513707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 170128975289207860283) ^ 85064487644603930141 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 170128975289207860283) ^ 24304139327029694326 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 170128975289207860283) ^ 256446589191898 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 170128975289207860283) ^ 9287726 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_547029240865032124721 : Nat.Prime 547029240865032124721 := by
  apply lucas_primality 547029240865032124721 (19 : ZMod 547029240865032124721)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (127, 1), (131149, 1), (410536570733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (127, 1), (131149, 1), (410536570733, 1)] : List FactorBlock).map factorBlockValue).prod) = 547029240865032124721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_127
      · exact prime_oneHundredFiftySevenEY_131149
      · exact prime_oneHundredFiftySevenEY_410536570733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 547029240865032124721) ^ 273514620432516062360 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 547029240865032124721) ^ 109405848173006424944 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 547029240865032124721) ^ 4307316857204977360 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 547029240865032124721) ^ 4171051558647280 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 547029240865032124721) ^ 1332473840 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_762961209196429638869 : Nat.Prime 762961209196429638869 := by
  apply lucas_primality 762961209196429638869 (2 : ZMod 762961209196429638869)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (43, 1), (557, 1), (19429, 1), (35999, 1), (1035107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (43, 1), (557, 1), (19429, 1), (35999, 1), (1035107, 1)] : List FactorBlock).map factorBlockValue).prod) = 762961209196429638869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_557
      · exact prime_oneHundredFiftySevenEY_19429
      · exact prime_oneHundredFiftySevenEY_35999
      · exact prime_oneHundredFiftySevenEY_1035107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 762961209196429638869) ^ 381480604598214819434 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 69360109926948148988 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 17743283934800689276 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 1369768777731471524 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 39269196005786692 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 21193955643113132 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 762961209196429638869) ^ 737084387600924 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_852114943727946022919 : Nat.Prime 852114943727946022919 := by
  apply lucas_primality 852114943727946022919 (7 : ZMod 852114943727946022919)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5981, 1), (414019, 1), (172057699381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5981, 1), (414019, 1), (172057699381, 1)] : List FactorBlock).map factorBlockValue).prod) = 852114943727946022919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5981
      · exact prime_oneHundredFiftySevenEY_414019
      · exact prime_oneHundredFiftySevenEY_172057699381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 852114943727946022919) ^ 426057471863973011459 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 852114943727946022919) ^ 142470313280044478 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 852114943727946022919) ^ 2058154199995522 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 852114943727946022919) ^ 4952495278 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1367827917966235946251 : Nat.Prime 1367827917966235946251 := by
  apply lucas_primality 1367827917966235946251 (3 : ZMod 1367827917966235946251)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 4), (2879, 1), (4692397198843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 4), (2879, 1), (4692397198843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1367827917966235946251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_2879
      · exact prime_oneHundredFiftySevenEY_4692397198843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1367827917966235946251) ^ 683913958983117973125 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367827917966235946251) ^ 455942639322078648750 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367827917966235946251) ^ 273565583593247189250 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367827917966235946251) ^ 475105216382853750 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1367827917966235946251) ^ 291498750 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2496835952629436316401 : Nat.Prime 2496835952629436316401 := by
  apply lucas_primality 2496835952629436316401 (3 : ZMod 2496835952629436316401)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (601, 1), (301577, 1), (34439538983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (601, 1), (301577, 1), (34439538983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2496835952629436316401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_601
      · exact prime_oneHundredFiftySevenEY_301577
      · exact prime_oneHundredFiftySevenEY_34439538983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2496835952629436316401) ^ 1248417976314718158200 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496835952629436316401) ^ 499367190525887263280 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496835952629436316401) ^ 4154469139150476400 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496835952629436316401) ^ 8279265171513200 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496835952629436316401) ^ 72499110800 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_3034528518056090630713 : Nat.Prime 3034528518056090630713 := by
  apply lucas_primality 3034528518056090630713 (11 : ZMod 3034528518056090630713)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (41, 1), (107, 1), (993835141855931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (41, 1), (107, 1), (993835141855931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3034528518056090630713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_107
      · exact prime_oneHundredFiftySevenEY_993835141855931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3034528518056090630713) ^ 1517264259028045315356 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3034528518056090630713) ^ 1011509506018696876904 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3034528518056090630713) ^ 104638914415727263128 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3034528518056090630713) ^ 74012890684294893432 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3034528518056090630713) ^ 28360079608000847016 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 3034528518056090630713) ^ 3053352 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_5482608897014060154701 : Nat.Prime 5482608897014060154701 := by
  apply lucas_primality 5482608897014060154701 (3 : ZMod 5482608897014060154701)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (1118899774900828603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (1118899774900828603, 1)] : List FactorBlock).map factorBlockValue).prod) = 5482608897014060154701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_1118899774900828603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5482608897014060154701) ^ 2741304448507030077350 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482608897014060154701) ^ 1096521779402812030940 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482608897014060154701) ^ 783229842430580022100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5482608897014060154701) ^ 4900 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_5680092778452428527979 : Nat.Prime 5680092778452428527979 := by
  apply lucas_primality 5680092778452428527979 (2 : ZMod 5680092778452428527979)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (5711, 1), (23971, 1), (50867, 1), (1210211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (5711, 1), (23971, 1), (50867, 1), (1210211, 1)] : List FactorBlock).map factorBlockValue).prod) = 5680092778452428527979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_337
      · exact prime_oneHundredFiftySevenEY_5711
      · exact prime_oneHundredFiftySevenEY_23971
      · exact prime_oneHundredFiftySevenEY_50867
      · exact prime_oneHundredFiftySevenEY_1210211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5680092778452428527979) ^ 2840046389226214263989 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5680092778452428527979) ^ 16854874713508689994 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5680092778452428527979) ^ 994588124400705398 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5680092778452428527979) ^ 236956855302341518 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5680092778452428527979) ^ 111665574507095534 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5680092778452428527979) ^ 4693473103824398 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_6103689673571437110953 : Nat.Prime 6103689673571437110953 := by
  apply lucas_primality 6103689673571437110953 (3 : ZMod 6103689673571437110953)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (762961209196429638869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (762961209196429638869, 1)] : List FactorBlock).map factorBlockValue).prod) = 6103689673571437110953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_762961209196429638869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6103689673571437110953) ^ 3051844836785718555476 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6103689673571437110953) ^ 8 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_6108863550676255832273 : Nat.Prime 6108863550676255832273 := by
  apply lucas_primality 6108863550676255832273 (3 : ZMod 6108863550676255832273)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (313, 1), (643, 1), (1897077755117863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (313, 1), (643, 1), (1897077755117863, 1)] : List FactorBlock).map factorBlockValue).prod) = 6108863550676255832273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_313
      · exact prime_oneHundredFiftySevenEY_643
      · exact prime_oneHundredFiftySevenEY_1897077755117863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6108863550676255832273) ^ 3054431775338127916136 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6108863550676255832273) ^ 19517135944652574544 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6108863550676255832273) ^ 9500565397630257904 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6108863550676255832273) ^ 3220144 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_40123832985913573646279 : Nat.Prime 40123832985913573646279 := by
  apply lucas_primality 40123832985913573646279 (19 : ZMod 40123832985913573646279)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (7067922553, 1), (97877448247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (7067922553, 1), (97877448247, 1)] : List FactorBlock).map factorBlockValue).prod) = 40123832985913573646279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_29
      · exact prime_oneHundredFiftySevenEY_7067922553
      · exact prime_oneHundredFiftySevenEY_97877448247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 40123832985913573646279) ^ 20061916492956786823139 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 40123832985913573646279) ^ 1383580447790123229182 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 40123832985913573646279) ^ 5676891998326 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 40123832985913573646279) ^ 409939508074 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_40752920534033374818847 : Nat.Prime 40752920534033374818847 := by
  apply lucas_primality 40752920534033374818847 (3 : ZMod 40752920534033374818847)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1043543, 1), (21703967, 1), (299887261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1043543, 1), (21703967, 1), (299887261, 1)] : List FactorBlock).map factorBlockValue).prod) = 40752920534033374818847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_1043543
      · exact prime_oneHundredFiftySevenEY_21703967
      · exact prime_oneHundredFiftySevenEY_299887261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40752920534033374818847) ^ 20376460267016687409423 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40752920534033374818847) ^ 13584306844677791606282 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40752920534033374818847) ^ 39052459298786322 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40752920534033374818847) ^ 1877671512034338 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40752920534033374818847) ^ 135894137010486 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_132158463222826084193453 : Nat.Prime 132158463222826084193453 := by
  apply lucas_primality 132158463222826084193453 (2 : ZMod 132158463222826084193453)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (491, 1), (2170659996432988703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (491, 1), (2170659996432988703, 1)] : List FactorBlock).map factorBlockValue).prod) = 132158463222826084193453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_31
      · exact prime_oneHundredFiftySevenEY_491
      · exact prime_oneHundredFiftySevenEY_2170659996432988703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 132158463222826084193453) ^ 66079231611413042096726 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 132158463222826084193453) ^ 4263176232994389812692 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 132158463222826084193453) ^ 269161839557690599172 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 132158463222826084193453) ^ 60884 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_150455380997348711365447 : Nat.Prime 150455380997348711365447 := by
  apply lucas_primality 150455380997348711365447 (3 : ZMod 150455380997348711365447)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (66598997, 1), (125506879294751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (66598997, 1), (125506879294751, 1)] : List FactorBlock).map factorBlockValue).prod) = 150455380997348711365447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_66598997
      · exact prime_oneHundredFiftySevenEY_125506879294751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150455380997348711365447) ^ 75227690498674355682723 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 150455380997348711365447) ^ 50151793665782903788482 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 150455380997348711365447) ^ 2259123827305518 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 150455380997348711365447) ^ 1198781946 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_184790993807785168128757 : Nat.Prime 184790993807785168128757 := by
  apply lucas_primality 184790993807785168128757 (2 : ZMod 184790993807785168128757)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (8081, 1), (15004817837488049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (8081, 1), (15004817837488049, 1)] : List FactorBlock).map factorBlockValue).prod) = 184790993807785168128757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_127
      · exact prime_oneHundredFiftySevenEY_8081
      · exact prime_oneHundredFiftySevenEY_15004817837488049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184790993807785168128757) ^ 92395496903892584064378 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184790993807785168128757) ^ 61596997935928389376252 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184790993807785168128757) ^ 1455047195336891087628 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184790993807785168128757) ^ 22867342384331786676 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 184790993807785168128757) ^ 12315444 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_185614415888816010591199 : Nat.Prime 185614415888816010591199 := by
  apply lucas_primality 185614415888816010591199 (3 : ZMod 185614415888816010591199)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (41, 1), (77081, 1), (296630166648581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (41, 1), (77081, 1), (296630166648581, 1)] : List FactorBlock).map factorBlockValue).prod) = 185614415888816010591199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_41
      · exact prime_oneHundredFiftySevenEY_77081
      · exact prime_oneHundredFiftySevenEY_296630166648581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185614415888816010591199) ^ 92807207944408005295599 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 185614415888816010591199) ^ 61871471962938670197066 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 185614415888816010591199) ^ 16874037808074182781018 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 185614415888816010591199) ^ 4527180875336975868078 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 185614415888816010591199) ^ 2408043692853180558 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 185614415888816010591199) ^ 625743558 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_194942536581827493910441 : Nat.Prime 194942536581827493910441 := by
  apply lucas_primality 194942536581827493910441 (19 : ZMod 194942536581827493910441)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (61, 1), (807014971774414199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (61, 1), (807014971774414199, 1)] : List FactorBlock).map factorBlockValue).prod) = 194942536581827493910441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_61
      · exact prime_oneHundredFiftySevenEY_807014971774414199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 194942536581827493910441) ^ 97471268290913746955220 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 194942536581827493910441) ^ 64980845527275831303480 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 194942536581827493910441) ^ 38988507316365498782088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 194942536581827493910441) ^ 17722048780166135810040 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 194942536581827493910441) ^ 3195779288226680228040 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (19 : ZMod 194942536581827493910441) ^ 241560 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_215977097223423038127029 : Nat.Prime 215977097223423038127029 := by
  apply lucas_primality 215977097223423038127029 (2 : ZMod 215977097223423038127029)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2377, 1), (22715302610793335941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2377, 1), (22715302610793335941, 1)] : List FactorBlock).map factorBlockValue).prod) = 215977097223423038127029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_2377
      · exact prime_oneHundredFiftySevenEY_22715302610793335941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215977097223423038127029) ^ 107988548611711519063514 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 215977097223423038127029) ^ 90861210443173343764 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 215977097223423038127029) ^ 9508 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_279786411027920655270091 : Nat.Prime 279786411027920655270091 := by
  apply lucas_primality 279786411027920655270091 (2 : ZMod 279786411027920655270091)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (23, 1), (386047, 1), (2942179252759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (23, 1), (386047, 1), (2942179252759, 1)] : List FactorBlock).map factorBlockValue).prod) = 279786411027920655270091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_23
      · exact prime_oneHundredFiftySevenEY_386047
      · exact prime_oneHundredFiftySevenEY_2942179252759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 279786411027920655270091) ^ 139893205513960327635045 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 93262137009306885090030 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 55957282205584131054018 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 39969487289702950752870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 16458024178112979721770 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 12164626566431332837830 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 724747015332124470 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 279786411027920655270091) ^ 95094957510 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_690977488586979470194037 : Nat.Prime 690977488586979470194037 := by
  apply lucas_primality 690977488586979470194037 (5 : ZMod 690977488586979470194037)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (59, 1), (51839, 1), (3322357473707177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (59, 1), (51839, 1), (3322357473707177, 1)] : List FactorBlock).map factorBlockValue).prod) = 690977488586979470194037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_59
      · exact prime_oneHundredFiftySevenEY_51839
      · exact prime_oneHundredFiftySevenEY_3322357473707177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 690977488586979470194037) ^ 345488744293489735097018 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 690977488586979470194037) ^ 40645734622763498246708 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 690977488586979470194037) ^ 11711482857406431698204 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 690977488586979470194037) ^ 13329298184513194124 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 690977488586979470194037) ^ 207978068 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1240847533252287089333929 : Nat.Prime 1240847533252287089333929 := by
  apply lucas_primality 1240847533252287089333929 (11 : ZMod 1240847533252287089333929)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (8233, 1), (238719527, 1), (2922931313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (8233, 1), (238719527, 1), (2922931313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1240847533252287089333929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_8233
      · exact prime_oneHundredFiftySevenEY_238719527
      · exact prime_oneHundredFiftySevenEY_2922931313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1240847533252287089333929) ^ 620423766626143544666964 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1240847533252287089333929) ^ 413615844417429029777976 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1240847533252287089333929) ^ 150716328586455373416 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1240847533252287089333929) ^ 5197930595984664 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (11 : ZMod 1240847533252287089333929) ^ 424521619010856 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_1698426169664673027160447 : Nat.Prime 1698426169664673027160447 := by
  apply lucas_primality 1698426169664673027160447 (3 : ZMod 1698426169664673027160447)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (202004361829, 1), (1401311465329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (202004361829, 1), (1401311465329, 1)] : List FactorBlock).map factorBlockValue).prod) = 1698426169664673027160447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_202004361829
      · exact prime_oneHundredFiftySevenEY_1401311465329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1698426169664673027160447) ^ 849213084832336513580223 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1698426169664673027160447) ^ 566142056554891009053482 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1698426169664673027160447) ^ 8407868791974 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1698426169664673027160447) ^ 1212026170974 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_2895949774618037617899739 : Nat.Prime 2895949774618037617899739 := by
  apply lucas_primality 2895949774618037617899739 (2 : ZMod 2895949774618037617899739)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2239, 1), (108630077, 1), (180402648431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2239, 1), (108630077, 1), (180402648431, 1)] : List FactorBlock).map factorBlockValue).prod) = 2895949774618037617899739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_11
      · exact prime_oneHundredFiftySevenEY_2239
      · exact prime_oneHundredFiftySevenEY_108630077
      · exact prime_oneHundredFiftySevenEY_180402648431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2895949774618037617899739) ^ 1447974887309018808949869 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2895949774618037617899739) ^ 965316591539345872633246 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2895949774618037617899739) ^ 263268161328912510718158 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2895949774618037617899739) ^ 1293412136944188306342 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2895949774618037617899739) ^ 26658820969242594 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2895949774618037617899739) ^ 16052700998598 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_4454745981331584254188777 : Nat.Prime 4454745981331584254188777 := by
  apply lucas_primality 4454745981331584254188777 (10 : ZMod 4454745981331584254188777)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (185614415888816010591199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (185614415888816010591199, 1)] : List FactorBlock).map factorBlockValue).prod) = 4454745981331584254188777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_185614415888816010591199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4454745981331584254188777) ^ 2227372990665792127094388 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4454745981331584254188777) ^ 1484915327110528084729592 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (10 : ZMod 4454745981331584254188777) ^ 24 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_11224957716747890730484021 : Nat.Prime 11224957716747890730484021 := by
  apply lucas_primality 11224957716747890730484021 (2 : ZMod 11224957716747890730484021)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (1549, 1), (30493, 1), (440087853767459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (1549, 1), (30493, 1), (440087853767459, 1)] : List FactorBlock).map factorBlockValue).prod) = 11224957716747890730484021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_1549
      · exact prime_oneHundredFiftySevenEY_30493
      · exact prime_oneHundredFiftySevenEY_440087853767459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11224957716747890730484021) ^ 5612478858373945365242010 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11224957716747890730484021) ^ 3741652572249296910161340 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11224957716747890730484021) ^ 2244991543349578146096804 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11224957716747890730484021) ^ 7246583419462808734980 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11224957716747890730484021) ^ 368115886162328755140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 11224957716747890730484021) ^ 25506174780 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_17473020879614338804413421 : Nat.Prime 17473020879614338804413421 := by
  apply lucas_primality 17473020879614338804413421 (2 : ZMod 17473020879614338804413421)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (16741, 1), (5798479076523484859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (16741, 1), (5798479076523484859, 1)] : List FactorBlock).map factorBlockValue).prod) = 17473020879614338804413421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_16741
      · exact prime_oneHundredFiftySevenEY_5798479076523484859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17473020879614338804413421) ^ 8736510439807169402206710 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17473020879614338804413421) ^ 5824340293204779601471140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17473020879614338804413421) ^ 3494604175922867760882684 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17473020879614338804413421) ^ 1043726233774227274620 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17473020879614338804413421) ^ 3013380 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_150174677026005761423368747 : Nat.Prime 150174677026005761423368747 := by
  apply lucas_primality 150174677026005761423368747 (12 : ZMod 150174677026005761423368747)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 1), (20286829, 1), (1587852908632427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 1), (20286829, 1), (1587852908632427, 1)] : List FactorBlock).map factorBlockValue).prod) = 150174677026005761423368747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_7
      · exact prime_oneHundredFiftySevenEY_37
      · exact prime_oneHundredFiftySevenEY_20286829
      · exact prime_oneHundredFiftySevenEY_1587852908632427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 150174677026005761423368747) ^ 75087338513002880711684373 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 150174677026005761423368747) ^ 50058225675335253807789582 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 150174677026005761423368747) ^ 21453525289429394489052678 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 150174677026005761423368747) ^ 4058775054756912470901858 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 150174677026005761423368747) ^ 7402570260044374674 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (12 : ZMod 150174677026005761423368747) ^ 94577196798 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_383503927281287440329098701 : Nat.Prime 383503927281287440329098701 := by
  apply lucas_primality 383503927281287440329098701 (2 : ZMod 383503927281287440329098701)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (17, 1), (52153, 1), (82387, 1), (17500951257067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (17, 1), (52153, 1), (82387, 1), (17500951257067, 1)] : List FactorBlock).map factorBlockValue).prod) = 383503927281287440329098701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_17
      · exact prime_oneHundredFiftySevenEY_52153
      · exact prime_oneHundredFiftySevenEY_82387
      · exact prime_oneHundredFiftySevenEY_17500951257067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 383503927281287440329098701) ^ 191751963640643720164549350 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 127834642427095813443032900 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 76700785456257488065819740 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 22559054545958084725241100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 7353439443201492537900 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 4654908265640057780100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 383503927281287440329098701) ^ 21913318976100 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_9769257937060164269435987959 : Nat.Prime 9769257937060164269435987959 := by
  apply lucas_primality 9769257937060164269435987959 (7 : ZMod 9769257937060164269435987959)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (536561, 1), (3034528518056090630713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (536561, 1), (3034528518056090630713, 1)] : List FactorBlock).map factorBlockValue).prod) = 9769257937060164269435987959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_536561
      · exact prime_oneHundredFiftySevenEY_3034528518056090630713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9769257937060164269435987959) ^ 4884628968530082134717993979 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 9769257937060164269435987959) ^ 3256419312353388089811995986 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 9769257937060164269435987959) ^ 18207171108336543784278 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (7 : ZMod 9769257937060164269435987959) ^ 3219366 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_15467991733678593426606980939 : Nat.Prime 15467991733678593426606980939 := by
  apply lucas_primality 15467991733678593426606980939 (2 : ZMod 15467991733678593426606980939)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (53, 1), (11224957716747890730484021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (53, 1), (11224957716747890730484021, 1)] : List FactorBlock).map factorBlockValue).prod) = 15467991733678593426606980939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_13
      · exact prime_oneHundredFiftySevenEY_53
      · exact prime_oneHundredFiftySevenEY_11224957716747890730484021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15467991733678593426606980939) ^ 7733995866839296713303490469 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15467991733678593426606980939) ^ 1189845517975276417431306226 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15467991733678593426606980939) ^ 291848900635445158992584546 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15467991733678593426606980939) ^ 1378 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_18561590080414312111928377121 : Nat.Prime 18561590080414312111928377121 := by
  apply lucas_primality 18561590080414312111928377121 (3 : ZMod 18561590080414312111928377121)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (157, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (157, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 18561590080414312111928377121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_157
      · exact prime_oneHundredFiftySevenEY_171401
      · exact prime_oneHundredFiftySevenEY_714027719
      · exact prime_oneHundredFiftySevenEY_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18561590080414312111928377121) ^ 9280795040207156055964188560 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561590080414312111928377121) ^ 3712318016082862422385675424 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561590080414312111928377121) ^ 118226688410282242751136160 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561590080414312111928377121) ^ 108293359317707085209120 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561590080414312111928377121) ^ 25995615557348288480 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18561590080414312111928377121) ^ 3074312834415693280 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_23201987600517890139910471403 : Nat.Prime 23201987600517890139910471403 := by
  apply lucas_primality 23201987600517890139910471403 (2 : ZMod 23201987600517890139910471403)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1360607, 1), (75278293, 1), (2634051583357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1360607, 1), (75278293, 1), (2634051583357, 1)] : List FactorBlock).map factorBlockValue).prod) = 23201987600517890139910471403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_43
      · exact prime_oneHundredFiftySevenEY_1360607
      · exact prime_oneHundredFiftySevenEY_75278293
      · exact prime_oneHundredFiftySevenEY_2634051583357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23201987600517890139910471403) ^ 11600993800258945069955235701 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 23201987600517890139910471403) ^ 539581106988788142788615614 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 23201987600517890139910471403) ^ 17052673990739346585686 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 23201987600517890139910471403) ^ 308216175950189122114 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 23201987600517890139910471403) ^ 8808478826731186 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_26516557257734731588469110177 : Nat.Prime 26516557257734731588469110177 := by
  apply lucas_primality 26516557257734731588469110177 (5 : ZMod 26516557257734731588469110177)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2333, 1), (2711, 1), (25301, 1), (96737, 1), (17843142601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2333, 1), (2711, 1), (25301, 1), (96737, 1), (17843142601, 1)] : List FactorBlock).map factorBlockValue).prod) = 26516557257734731588469110177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_2333
      · exact prime_oneHundredFiftySevenEY_2711
      · exact prime_oneHundredFiftySevenEY_25301
      · exact prime_oneHundredFiftySevenEY_96737
      · exact prime_oneHundredFiftySevenEY_17843142601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26516557257734731588469110177) ^ 13258278628867365794234555088 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 8838852419244910529489703392 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 11365862519389083406973472 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 9781098213845345477118816 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 1048043842446335385497376 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 274109774519932720556448 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 26516557257734731588469110177) ^ 1486092324131772576 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_30935983467357186853213961881 : Nat.Prime 30935983467357186853213961881 := by
  apply lucas_primality 30935983467357186853213961881 (13 : ZMod 30935983467357186853213961881)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (39345491, 1), (130747447, 1), (50113472137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (39345491, 1), (130747447, 1), (50113472137, 1)] : List FactorBlock).map factorBlockValue).prod) = 30935983467357186853213961881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_39345491
      · exact prime_oneHundredFiftySevenEY_130747447
      · exact prime_oneHundredFiftySevenEY_50113472137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 30935983467357186853213961881) ^ 15467991733678593426606980940 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 30935983467357186853213961881) ^ 10311994489119062284404653960 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 30935983467357186853213961881) ^ 6187196693471437370642792376 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 30935983467357186853213961881) ^ 786265025066206108680 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 30935983467357186853213961881) ^ 236608700033410112040 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (13 : ZMod 30935983467357186853213961881) ^ 617318699905377240 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_37123180160828624223856754243 : Nat.Prime 37123180160828624223856754243 := by
  apply lucas_primality 37123180160828624223856754243 (2 : ZMod 37123180160828624223856754243)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18561590080414312111928377121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18561590080414312111928377121, 1)] : List FactorBlock).map factorBlockValue).prod) = 37123180160828624223856754243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_18561590080414312111928377121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37123180160828624223856754243) ^ 18561590080414312111928377121 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 37123180160828624223856754243) ^ 2 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_37123180160828624223856754257 : Nat.Prime 37123180160828624223856754257 := by
  apply lucas_primality 37123180160828624223856754257 (5 : ZMod 37123180160828624223856754257)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (39345491, 1), (130747447, 1), (50113472137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (39345491, 1), (130747447, 1), (50113472137, 1)] : List FactorBlock).map factorBlockValue).prod) = 37123180160828624223856754257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_3
      · exact prime_oneHundredFiftySevenEY_39345491
      · exact prime_oneHundredFiftySevenEY_130747447
      · exact prime_oneHundredFiftySevenEY_50113472137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37123180160828624223856754257) ^ 18561590080414312111928377128 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 37123180160828624223856754257) ^ 12374393386942874741285584752 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 37123180160828624223856754257) ^ 943518030079447330416 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 37123180160828624223856754257) ^ 283930440040092134448 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (5 : ZMod 37123180160828624223856754257) ^ 740782439886452688 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySevenEY_61871966934714373706427923741 : Nat.Prime 61871966934714373706427923741 := by
  apply lucas_primality 61871966934714373706427923741 (2 : ZMod 61871966934714373706427923741)
  · rw [← oneHundredFiftySevenEYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11057, 1), (279786411027920655270091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11057, 1), (279786411027920655270091, 1)] : List FactorBlock).map factorBlockValue).prod) = 61871966934714373706427923741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySevenEY_2
      · exact prime_oneHundredFiftySevenEY_5
      · exact prime_oneHundredFiftySevenEY_11057
      · exact prime_oneHundredFiftySevenEY_279786411027920655270091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61871966934714373706427923741) ^ 30935983467357186853213961870 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 61871966934714373706427923741) ^ 12374393386942874741285584748 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 61871966934714373706427923741) ^ 5595728220558413105401820 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide
    · change (2 : ZMod 61871966934714373706427923741) ^ 221140 ≠ 1
      rw [← oneHundredFiftySevenEYFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771200 : Nat.totient 185615900804143121119283771200 = 73773023038106923735087104000 := by
  rw [← show ((([(2, 6), (5, 2), (157, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_157, prime_oneHundredFiftySevenEY_171401, prime_oneHundredFiftySevenEY_714027719, prime_oneHundredFiftySevenEY_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771201 : Nat.totient 185615900804143121119283771201 = 184942859962912511400108672000 := by
  rw [← show ((([(281, 1), (14813, 1), (9908192201, 1), (4500610324117, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_281, prime_oneHundredFiftySevenEY_14813, prime_oneHundredFiftySevenEY_9908192201, prime_oneHundredFiftySevenEY_4500610324117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771202 : Nat.totient 185615900804143121119283771202 = 58615438379334335597333905920 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (536561, 1), (3034528518056090630713, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_536561, prime_oneHundredFiftySevenEY_3034528518056090630713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771203 : Nat.totient 185615900804143121119283771203 = 177128189373275057487040413696 := by
  rw [← show ((([(37, 1), (53, 1), (2789, 1), (48071526703, 1), (705994234369, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_37, prime_oneHundredFiftySevenEY_53, prime_oneHundredFiftySevenEY_2789, prime_oneHundredFiftySevenEY_48071526703, prime_oneHundredFiftySevenEY_705994234369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771204 : Nat.totient 185615900804143121119283771204 = 71991786096645570379097838720 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (71, 1), (179, 1), (40123832985913573646279, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_71, prime_oneHundredFiftySevenEY_179, prime_oneHundredFiftySevenEY_40123832985913573646279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771205 : Nat.totient 185615900804143121119283771205 = 98971979497346053629341445888 := by
  rw [← show ((([(3, 1), (5, 1), (4273, 1), (2895949774618037617899739, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_4273, prime_oneHundredFiftySevenEY_2895949774618037617899739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771206 : Nat.totient 185615900804143121119283771206 = 92807950361837506843983992928 := by
  rw [← show ((([(2, 1), (2306701459, 1), (40234053713351191217, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_2306701459, prime_oneHundredFiftySevenEY_40234053713351191217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771207 : Nat.totient 185615900804143121119283771207 = 168715250353930578363321259680 := by
  rw [← show ((([(11, 1), (6373, 1), (3215386423, 1), (823465483808503, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_6373, prime_oneHundredFiftySevenEY_3215386423, prime_oneHundredFiftySevenEY_823465483808503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771208 : Nat.totient 185615900804143121119283771208 = 56209717428124687113173760000 := by
  rw [← show ((([(2, 3), (3, 2), (17, 1), (29, 1), (3823, 1), (1367827917966235946251, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_29, prime_oneHundredFiftySevenEY_3823, prime_oneHundredFiftySevenEY_1367827917966235946251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771209 : Nat.totient 185615900804143121119283771209 = 185615900614016643362071195296 := by
  rw [← show ((([(1431883433, 1), (3330836407, 1), (38918331239, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_1431883433, prime_oneHundredFiftySevenEY_3330836407, prime_oneHundredFiftySevenEY_38918331239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771210 : Nat.totient 185615900804143121119283771210 = 74246360321657248447713508480 := by
  rw [← show ((([(2, 1), (5, 1), (18561590080414312111928377121, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_18561590080414312111928377121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771211 : Nat.totient 185615900804143121119283771211 = 106066228678578910821748365216 := by
  rw [← show ((([(3, 1), (7, 1), (341689847, 1), (4574292847, 1), (5655094199, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_341689847, prime_oneHundredFiftySevenEY_4574292847, prime_oneHundredFiftySevenEY_5655094199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771212 : Nat.totient 185615900804143121119283771212 = 88725577404024247238181812160 := by
  rw [← show ((([(2, 2), (23, 1), (1879, 1), (26969690519, 1), (39812972784661, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_23, prime_oneHundredFiftySevenEY_1879, prime_oneHundredFiftySevenEY_26969690519, prime_oneHundredFiftySevenEY_39812972784661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771213 : Nat.totient 185615900804143121119283771213 = 185356552011690483964100812800 := by
  rw [← show ((([(769, 1), (10313, 1), (213247379, 1), (109753939517351, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_769, prime_oneHundredFiftySevenEY_10313, prime_oneHundredFiftySevenEY_213247379, prime_oneHundredFiftySevenEY_109753939517351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771214 : Nat.totient 185615900804143121119283771214 = 61870410463749813501494236800 := by
  rw [← show ((([(2, 1), (3, 1), (51131, 1), (178609, 1), (3387476581164248711, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_51131, prime_oneHundredFiftySevenEY_178609, prime_oneHundredFiftySevenEY_3387476581164248711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771215 : Nat.totient 185615900804143121119283771215 = 148492720643314496895427016968 := by
  rw [← show ((([(5, 1), (37123180160828624223856754243, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_37123180160828624223856754243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771216 : Nat.totient 185615900804143121119283771216 = 90649558145488738909409874432 := by
  rw [← show ((([(2, 4), (43, 1), (1360607, 1), (75278293, 1), (2634051583357, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_43, prime_oneHundredFiftySevenEY_1360607, prime_oneHundredFiftySevenEY_75278293, prime_oneHundredFiftySevenEY_2634051583357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771217 : Nat.totient 185615900804143121119283771217 = 114225132977767873603836173376 := by
  rw [← show ((([(3, 3), (13, 1), (3108349, 1), (170128975289207860283, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_3108349, prime_oneHundredFiftySevenEY_170128975289207860283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771218 : Nat.totient 185615900804143121119283771218 = 72308856107325790682233347600 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (8011, 1), (150455380997348711365447, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_8011, prime_oneHundredFiftySevenEY_150455380997348711365447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771219 : Nat.totient 185615900804143121119283771219 = 184835394757377067952507466240 := by
  rw [← show ((([(241, 1), (19603, 1), (208589, 1), (188358053082422677, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_241, prime_oneHundredFiftySevenEY_19603, prime_oneHundredFiftySevenEY_208589, prime_oneHundredFiftySevenEY_188358053082422677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771220 : Nat.totient 185615900804143121119283771220 = 49493096965195052234657840640 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11057, 1), (279786411027920655270091, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_11057, prime_oneHundredFiftySevenEY_279786411027920655270091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771221 : Nat.totient 185615900804143121119283771221 = 175846642867082956849847783244 := by
  rw [← show ((([(19, 1), (9769257937060164269435987959, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_9769257937060164269435987959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771222 : Nat.totient 185615900804143121119283771222 = 92807950402064125714001960824 := by
  rw [← show ((([(2, 1), (12503863767119, 1), (7422341776157669, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_12503863767119, prime_oneHundredFiftySevenEY_7422341776157669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771223 : Nat.totient 185615900804143121119283771223 = 123743933869428747412855847480 := by
  rw [← show ((([(3, 1), (61871966934714373706427923741, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_61871966934714373706427923741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771224 : Nat.totient 185615900804143121119283771224 = 92807950402071560559641885608 := by
  rw [← show ((([(2, 3), (23201987600517890139910471403, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_23201987600517890139910471403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771225 : Nat.totient 185615900804143121119283771225 = 119791854070249133373939448320 := by
  rw [← show ((([(5, 2), (7, 2), (17, 1), (202067, 1), (44109767997717924059, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_202067, prime_oneHundredFiftySevenEY_44109767997717924059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771226 : Nat.totient 185615900804143121119283771226 = 59874998369453312341079177280 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (54499, 1), (6103689673571437110953, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_31, prime_oneHundredFiftySevenEY_54499, prime_oneHundredFiftySevenEY_6103689673571437110953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771227 : Nat.totient 185615900804143121119283771227 = 184122645785751650313459543840 := by
  rw [← show ((([(127, 1), (5807, 1), (12595475021, 1), (19982281804183, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_127, prime_oneHundredFiftySevenEY_5807, prime_oneHundredFiftySevenEY_12595475021, prime_oneHundredFiftySevenEY_19982281804183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771228 : Nat.totient 185615900804143121119283771228 = 92802632505291016449732288000 := by
  rw [← show ((([(2, 2), (24793, 1), (82261, 1), (342071, 1), (532199, 1), (124980371, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_24793, prime_oneHundredFiftySevenEY_82261, prime_oneHundredFiftySevenEY_342071, prime_oneHundredFiftySevenEY_532199, prime_oneHundredFiftySevenEY_124980371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771229 : Nat.totient 185615900804143121119283771229 = 108292118336649040495910400000 := by
  rw [← show ((([(3, 1), (11, 1), (47, 1), (61, 1), (27551, 1), (45660169, 1), (1559547702281, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_47, prime_oneHundredFiftySevenEY_61, prime_oneHundredFiftySevenEY_27551, prime_oneHundredFiftySevenEY_45660169, prime_oneHundredFiftySevenEY_1559547702281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771230 : Nat.totient 185615900804143121119283771230 = 66748656267331275415841095680 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (41, 1), (1087, 1), (1297, 1), (36263, 1), (681168754045183, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_41, prime_oneHundredFiftySevenEY_1087, prime_oneHundredFiftySevenEY_1297, prime_oneHundredFiftySevenEY_36263, prime_oneHundredFiftySevenEY_681168754045183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771231 : Nat.totient 185615900804143121119283771231 = 185565190519302647881188814272 := by
  rw [← show ((([(3673, 1), (1060043, 1), (47672811646421489029, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3673, prime_oneHundredFiftySevenEY_1060043, prime_oneHundredFiftySevenEY_47672811646421489029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771232 : Nat.totient 185615900804143121119283771232 = 52988186798863905772339200000 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (2333, 1), (2711, 1), (25301, 1), (96737, 1), (17843142601, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_2333, prime_oneHundredFiftySevenEY_2711, prime_oneHundredFiftySevenEY_25301, prime_oneHundredFiftySevenEY_96737, prime_oneHundredFiftySevenEY_17843142601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771233 : Nat.totient 185615900804143121119283771233 = 185605335832213871380109317248 := by
  rw [← show ((([(17569, 1), (35830214219, 1), (294861947626403, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_17569, prime_oneHundredFiftySevenEY_35830214219, prime_oneHundredFiftySevenEY_294861947626403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771234 : Nat.totient 185615900804143121119283771234 = 92807950402069430012855237476 := by
  rw [← show ((([(2, 1), (44489649271439, 1), (2086057137376703, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_44489649271439, prime_oneHundredFiftySevenEY_2086057137376703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771235 : Nat.totient 185615900804143121119283771235 = 93086077887923998053826303104 := by
  rw [← show ((([(3, 2), (5, 1), (23, 2), (59, 1), (132158463222826084193453, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_23, prime_oneHundredFiftySevenEY_59, prime_oneHundredFiftySevenEY_132158463222826084193453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771236 : Nat.totient 185615900804143121119283771236 = 92806568447094386600701363232 := by
  rw [← show ((([(2, 2), (67157, 1), (690977488586979470194037, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_67157, prime_oneHundredFiftySevenEY_690977488586979470194037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771237 : Nat.totient 185615900804143121119283771237 = 179209894109527687841891850240 := by
  rw [← show ((([(29, 1), (32833, 1), (194942536581827493910441, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_29, prime_oneHundredFiftySevenEY_32833, prime_oneHundredFiftySevenEY_194942536581827493910441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771238 : Nat.totient 185615900804143121119283771238 = 61871955574528816801559975016 := by
  rw [← show ((([(2, 1), (3, 1), (5446387, 1), (5680092778452428527979, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5446387, prime_oneHundredFiftySevenEY_5680092778452428527979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771239 : Nat.totient 185615900804143121119283771239 = 159099343546408389530814661056 := by
  rw [← show ((([(7, 1), (26516557257734731588469110177, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_26516557257734731588469110177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771240 : Nat.totient 185615900804143121119283771240 = 62129719909327569074920488960 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (19, 1), (37, 1), (797, 1), (15013, 1), (15193, 1), (3300941532509, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_37, prime_oneHundredFiftySevenEY_797, prime_oneHundredFiftySevenEY_15013, prime_oneHundredFiftySevenEY_15193, prime_oneHundredFiftySevenEY_3300941532509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771241 : Nat.totient 185615900804143121119283771241 = 123740288406516667105704326400 := by
  rw [← show ((([(3, 1), (33961, 1), (70471187, 1), (25852459481259721, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_33961, prime_oneHundredFiftySevenEY_70471187, prime_oneHundredFiftySevenEY_25852459481259721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771242 : Nat.totient 185615900804143121119283771242 = 86479534623094748326676992000 := by
  rw [← show ((([(2, 1), (17, 1), (101, 1), (20177, 1), (777411659, 1), (3445936283891, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_101, prime_oneHundredFiftySevenEY_20177, prime_oneHundredFiftySevenEY_777411659, prime_oneHundredFiftySevenEY_3445936283891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771243 : Nat.totient 185615900804143121119283771243 = 171337754570375629762570718784 := by
  rw [← show ((([(13, 1), (9484948073, 1), (1505347852809833407, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_9484948073, prime_oneHundredFiftySevenEY_1505347852809833407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771244 : Nat.totient 185615900804143121119283771244 = 61871966930107298724183612000 := by
  rw [← show ((([(2, 2), (3, 4), (13429776301, 1), (42658088257671031, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_13429776301, prime_oneHundredFiftySevenEY_42658088257671031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771245 : Nat.totient 185615900804143121119283771245 = 147660412823172734273494087680 := by
  rw [← show ((([(5, 1), (181, 1), (12527, 1), (2237519, 1), (2857469, 1), (2560774057, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_181, prime_oneHundredFiftySevenEY_12527, prime_oneHundredFiftySevenEY_2237519, prime_oneHundredFiftySevenEY_2857469, prime_oneHundredFiftySevenEY_2560774057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771246 : Nat.totient 185615900804143121119283771246 = 79055388523043668185929410176 := by
  rw [← show ((([(2, 1), (7, 1), (163, 1), (12653, 1), (20692877189, 1), (310659864859, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_163, prime_oneHundredFiftySevenEY_12653, prime_oneHundredFiftySevenEY_20692877189, prime_oneHundredFiftySevenEY_310659864859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771247 : Nat.totient 185615900804143121119283771247 = 122068512002167248314648192000 := by
  rw [← show ((([(3, 1), (137, 1), (191, 1), (947, 1), (2496835952629436316401, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_137, prime_oneHundredFiftySevenEY_191, prime_oneHundredFiftySevenEY_947, prime_oneHundredFiftySevenEY_2496835952629436316401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771248 : Nat.totient 185615900804143121119283771248 = 91325187467757892370576245248 := by
  rw [← show ((([(2, 4), (67, 1), (937, 1), (184790993807785168128757, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_67, prime_oneHundredFiftySevenEY_937, prime_oneHundredFiftySevenEY_184790993807785168128757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771249 : Nat.totient 185615900804143121119283771249 = 185614951103590977129662843056 := by
  rw [← show ((([(323819, 1), (493013, 1), (1162664678671389767, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_323819, prime_oneHundredFiftySevenEY_493013, prime_oneHundredFiftySevenEY_1162664678671389767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771250 : Nat.totient 185615900804143121119283771250 = 49241962986373692219572160000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 4), (197, 1), (11311, 1), (22213484087755865417, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_197, prime_oneHundredFiftySevenEY_11311, prime_oneHundredFiftySevenEY_22213484087755865417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771251 : Nat.totient 185615900804143121119283771251 = 167208249856814261354589120000 := by
  rw [← show ((([(11, 1), (211, 1), (229, 1), (436439, 1), (800167674409054801, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_211, prime_oneHundredFiftySevenEY_229, prime_oneHundredFiftySevenEY_436439, prime_oneHundredFiftySevenEY_800167674409054801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771252 : Nat.totient 185615900804143121119283771252 = 92805468707005055985463142976 := by
  rw [← show ((([(2, 2), (37397, 1), (1240847533252287089333929, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_37397, prime_oneHundredFiftySevenEY_1240847533252287089333929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771253 : Nat.totient 185615900804143121119283771253 = 104874139937190766735154631168 := by
  rw [← show ((([(3, 2), (7, 1), (89, 1), (314267, 1), (105338187518725257337, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_89, prime_oneHundredFiftySevenEY_314267, prime_oneHundredFiftySevenEY_105338187518725257337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771254 : Nat.totient 185615900804143121119283771254 = 91853231656647115978477913088 := by
  rw [← show ((([(2, 1), (199, 1), (367, 1), (389, 1), (1299272743, 1), (2514294307297, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_199, prime_oneHundredFiftySevenEY_367, prime_oneHundredFiftySevenEY_389, prime_oneHundredFiftySevenEY_1299272743, prime_oneHundredFiftySevenEY_2514294307297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771255 : Nat.totient 185615900804143121119283771255 = 148115674622533620111599410080 := by
  rw [← show ((([(5, 1), (503, 1), (1811, 1), (40752920534033374818847, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_503, prime_oneHundredFiftySevenEY_1811, prime_oneHundredFiftySevenEY_40752920534033374818847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771256 : Nat.totient 185615900804143121119283771256 = 56034988922005470526576227840 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (53, 1), (11224957716747890730484021, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_53, prime_oneHundredFiftySevenEY_11224957716747890730484021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771257 : Nat.totient 185615900804143121119283771257 = 179628291097338102373810354080 := by
  rw [← show ((([(31, 1), (52133239439, 1), (114852055383311273, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_31, prime_oneHundredFiftySevenEY_52133239439, prime_oneHundredFiftySevenEY_114852055383311273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771258 : Nat.totient 185615900804143121119283771258 = 87465400345876375770429081600 := by
  rw [← show ((([(2, 1), (23, 1), (73, 1), (2053, 1), (2621, 1), (5711, 1), (1798731561437357, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_23, prime_oneHundredFiftySevenEY_73, prime_oneHundredFiftySevenEY_2053, prime_oneHundredFiftySevenEY_2621, prime_oneHundredFiftySevenEY_5711, prime_oneHundredFiftySevenEY_1798731561437357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771259 : Nat.totient 185615900804143121119283771259 = 107769214780373686277334868992 := by
  rw [← show ((([(3, 1), (17, 1), (19, 1), (43, 1), (4454745981331584254188777, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_43, prime_oneHundredFiftySevenEY_4454745981331584254188777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771260 : Nat.totient 185615900804143121119283771260 = 63500374035151324789293135360 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (463, 1), (33203, 1), (86243986962245050681, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_463, prime_oneHundredFiftySevenEY_33203, prime_oneHundredFiftySevenEY_86243986962245050681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771261 : Nat.totient 185615900804143121119283771261 = 185615900802962017434841170300 := by
  rw [← show ((([(157154640991, 1), (1181103527287959971, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_157154640991, prime_oneHundredFiftySevenEY_1181103527287959971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771262 : Nat.totient 185615900804143121119283771262 = 56071622585754433357824983040 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (433, 1), (1249, 1), (71147, 1), (79030999, 1), (308280169, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_433, prime_oneHundredFiftySevenEY_1249, prime_oneHundredFiftySevenEY_71147, prime_oneHundredFiftySevenEY_79030999, prime_oneHundredFiftySevenEY_308280169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771263 : Nat.totient 185615900804143121119283771263 = 183172908733870425745164288000 := by
  rw [← show ((([(97, 1), (347, 1), (8170697, 1), (87250601, 1), (7735465181, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_97, prime_oneHundredFiftySevenEY_347, prime_oneHundredFiftySevenEY_8170697, prime_oneHundredFiftySevenEY_87250601, prime_oneHundredFiftySevenEY_7735465181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771264 : Nat.totient 185615900804143121119283771264 = 91562558729728772749697187840 := by
  rw [← show ((([(2, 7), (79, 1), (1367, 1), (29363, 1), (200461, 1), (2281283630737, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_79, prime_oneHundredFiftySevenEY_1367, prime_oneHundredFiftySevenEY_29363, prime_oneHundredFiftySevenEY_200461, prime_oneHundredFiftySevenEY_2281283630737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771265 : Nat.totient 185615900804143121119283771265 = 98882780299226364945386741760 := by
  rw [← show ((([(3, 1), (5, 1), (881, 1), (190112907169, 1), (73881619525759, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_881, prime_oneHundredFiftySevenEY_190112907169, prime_oneHundredFiftySevenEY_73881619525759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771266 : Nat.totient 185615900804143121119283771266 = 89590011072260831041212408000 := by
  rw [← show ((([(2, 1), (29, 1), (5651, 1), (49547, 1), (11429954795135383141, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_29, prime_oneHundredFiftySevenEY_5651, prime_oneHundredFiftySevenEY_49547, prime_oneHundredFiftySevenEY_11429954795135383141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771267 : Nat.totient 185615900804143121119283771267 = 157458458039530619854221341184 := by
  rw [← show ((([(7, 1), (113, 1), (677, 1), (121275363467, 1), (2858100133843, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_113, prime_oneHundredFiftySevenEY_677, prime_oneHundredFiftySevenEY_121275363467, prime_oneHundredFiftySevenEY_2858100133843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771268 : Nat.totient 185615900804143121119283771268 = 61871966934714373706427923752 := by
  rw [← show ((([(2, 2), (3, 1), (15467991733678593426606980939, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_15467991733678593426606980939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771269 : Nat.totient 185615900804143121119283771269 = 171141928348991797378488191616 := by
  rw [← show ((([(13, 1), (919, 1), (18233, 1), (852114943727946022919, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_919, prime_oneHundredFiftySevenEY_18233, prime_oneHundredFiftySevenEY_852114943727946022919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771270 : Nat.totient 185615900804143121119283771270 = 73919635070978257237953331200 := by
  rw [← show ((([(2, 1), (5, 1), (233, 1), (12197, 1), (36781, 1), (220349681, 1), (805879807, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_233, prime_oneHundredFiftySevenEY_12197, prime_oneHundredFiftySevenEY_36781, prime_oneHundredFiftySevenEY_220349681, prime_oneHundredFiftySevenEY_805879807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771271 : Nat.totient 185615900804143121119283771271 = 120671075984488097591667271680 := by
  rw [← show ((([(3, 3), (41, 1), (2213, 1), (1102523, 1), (2380003, 1), (28874932649, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_41, prime_oneHundredFiftySevenEY_2213, prime_oneHundredFiftySevenEY_1102523, prime_oneHundredFiftySevenEY_2380003, prime_oneHundredFiftySevenEY_28874932649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771272 : Nat.totient 185615900804143121119283771272 = 92677300126300319746932601600 := by
  rw [← show ((([(2, 3), (719, 1), (58991, 1), (547029240865032124721, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_719, prime_oneHundredFiftySevenEY_58991, prime_oneHundredFiftySevenEY_547029240865032124721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771273 : Nat.totient 185615900804143121119283771273 = 168701293505066405523514588800 := by
  rw [← show ((([(11, 1), (4297, 1), (144829, 1), (27114500385628308511, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_4297, prime_oneHundredFiftySevenEY_144829, prime_oneHundredFiftySevenEY_27114500385628308511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771274 : Nat.totient 185615900804143121119283771274 = 53033114515371403324800221424 := by
  rw [← show ((([(2, 1), (3, 1), (7, 3), (542589269587, 1), (166225866747419, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_542589269587, prime_oneHundredFiftySevenEY_166225866747419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771275 : Nat.totient 185615900804143121119283771275 = 146369793690421733314646400000 := by
  rw [← show ((([(5, 2), (71, 1), (5843, 1), (22787, 1), (233264201, 1), (3367019941, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_71, prime_oneHundredFiftySevenEY_5843, prime_oneHundredFiftySevenEY_22787, prime_oneHundredFiftySevenEY_233264201, prime_oneHundredFiftySevenEY_3367019941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771276 : Nat.totient 185615900804143121119283771276 = 85471353061175650561697028096 := by
  rw [← show ((([(2, 2), (17, 1), (47, 1), (4729, 1), (114547, 1), (107214956384313287, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_47, prime_oneHundredFiftySevenEY_4729, prime_oneHundredFiftySevenEY_114547, prime_oneHundredFiftySevenEY_107214956384313287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771277 : Nat.totient 185615900804143121119283771277 = 120395775385605356304370597440 := by
  rw [← show ((([(3, 1), (37, 1), (32579, 1), (3736471, 1), (13737029566662823, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_37, prime_oneHundredFiftySevenEY_32579, prime_oneHundredFiftySevenEY_3736471, prime_oneHundredFiftySevenEY_13737029566662823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771278 : Nat.totient 185615900804143121119283771278 = 87591133651382804985262212096 := by
  rw [← show ((([(2, 1), (19, 1), (293, 1), (2729, 1), (6108863550676255832273, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_293, prime_oneHundredFiftySevenEY_2729, prime_oneHundredFiftySevenEY_6108863550676255832273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771279 : Nat.totient 185615900804143121119283771279 = 185615900804142258833528293776 := by
  rw [← show ((([(414763615828967, 1), (447522139648537, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_414763615828967, prime_oneHundredFiftySevenEY_447522139648537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771280 : Nat.totient 185615900804143121119283771280 = 49497571910185838540352276480 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (39345491, 1), (130747447, 1), (50113472137, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_39345491, prime_oneHundredFiftySevenEY_130747447, prime_oneHundredFiftySevenEY_50113472137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771281 : Nat.totient 185615900804143121119283771281 = 152181980783511600094405669008 := by
  rw [← show ((([(7, 1), (23, 1), (24316571578759, 1), (47411856152519, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_23, prime_oneHundredFiftySevenEY_24316571578759, prime_oneHundredFiftySevenEY_47411856152519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771282 : Nat.totient 185615900804143121119283771282 = 83721202730654828006599799040 := by
  rw [← show ((([(2, 1), (13, 1), (83, 1), (223, 1), (227, 1), (509, 1), (3338222149673586311, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_83, prime_oneHundredFiftySevenEY_223, prime_oneHundredFiftySevenEY_227, prime_oneHundredFiftySevenEY_509, prime_oneHundredFiftySevenEY_3338222149673586311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771283 : Nat.totient 185615900804143121119283771283 = 123708987827669518735247013600 := by
  rw [← show ((([(3, 1), (3541, 1), (17473020879614338804413421, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_3541, prime_oneHundredFiftySevenEY_17473020879614338804413421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771284 : Nat.totient 185615900804143121119283771284 = 84370864001883236872401714000 := by
  rw [← show ((([(2, 2), (11, 2), (383503927281287440329098701, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_383503927281287440329098701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771285 : Nat.totient 185615900804143121119283771285 = 148492720643314496895427017024 := by
  rw [← show ((([(5, 1), (37123180160828624223856754257, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_37123180160828624223856754257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771286 : Nat.totient 185615900804143121119283771286 = 61871966934714373706427923760 := by
  rw [← show ((([(2, 1), (3, 1), (30935983467357186853213961881, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_30935983467357186853213961881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771287 : Nat.totient 185615900804143121119283771287 = 185615900804142047671159534560 := by
  rw [← show ((([(216635296222567, 1), (856812828014161, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_216635296222567, prime_oneHundredFiftySevenEY_856812828014161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771288 : Nat.totient 185615900804143121119283771288 = 76982414347292353372849305600 := by
  rw [← show ((([(2, 3), (7, 1), (31, 1), (83761, 1), (350087, 1), (3646259878709069, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_31, prime_oneHundredFiftySevenEY_83761, prime_oneHundredFiftySevenEY_350087, prime_oneHundredFiftySevenEY_3646259878709069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771289 : Nat.totient 185615900804143121119283771289 = 123733743312410759374692811992 := by
  rw [← show ((([(3, 2), (12143, 1), (1698426169664673027160447, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_12143, prime_oneHundredFiftySevenEY_1698426169664673027160447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771290 : Nat.totient 185615900804143121119283771290 = 73028728814126243974970572800 := by
  rw [← show ((([(2, 1), (5, 1), (61, 1), (153313, 1), (42482513, 1), (46719282182381, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_61, prime_oneHundredFiftySevenEY_153313, prime_oneHundredFiftySevenEY_42482513, prime_oneHundredFiftySevenEY_46719282182381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771291 : Nat.totient 185615900804143121119283771291 = 185334230832434135819168505088 := by
  rw [← show ((([(659, 1), (26490377, 1), (10632652582618432337, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_659, prime_oneHundredFiftySevenEY_26490377, prime_oneHundredFiftySevenEY_10632652582618432337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771292 : Nat.totient 185615900804143121119283771292 = 61271268226610350660734448368 := by
  rw [← show ((([(2, 2), (3, 1), (103, 1), (150174677026005761423368747, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_103, prime_oneHundredFiftySevenEY_150174677026005761423368747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771293 : Nat.totient 185615900804143121119283771293 = 174524177289717419901597729792 := by
  rw [← show ((([(17, 1), (1009, 1), (85242719, 1), (126945641834432899, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_17, prime_oneHundredFiftySevenEY_1009, prime_oneHundredFiftySevenEY_85242719, prime_oneHundredFiftySevenEY_126945641834432899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771294 : Nat.totient 185615900804143121119283771294 = 91234925514381037371968717920 := by
  rw [← show ((([(2, 1), (59, 1), (10411757, 1), (7701644099, 1), (19616688731, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_59, prime_oneHundredFiftySevenEY_10411757, prime_oneHundredFiftySevenEY_7701644099, prime_oneHundredFiftySevenEY_19616688731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771295 : Nat.totient 185615900804143121119283771295 = 68439226002635441615929344000 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (29, 1), (257, 1), (2281, 1), (9883, 1), (19181, 1), (32363, 1), (118529, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_7, prime_oneHundredFiftySevenEY_11, prime_oneHundredFiftySevenEY_13, prime_oneHundredFiftySevenEY_29, prime_oneHundredFiftySevenEY_257, prime_oneHundredFiftySevenEY_2281, prime_oneHundredFiftySevenEY_9883, prime_oneHundredFiftySevenEY_19181, prime_oneHundredFiftySevenEY_32363, prime_oneHundredFiftySevenEY_118529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771296 : Nat.totient 185615900804143121119283771296 = 91574289222731368165859872000 := by
  rw [← show ((([(2, 5), (107, 1), (251, 1), (215977097223423038127029, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_107, prime_oneHundredFiftySevenEY_251, prime_oneHundredFiftySevenEY_215977097223423038127029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771297 : Nat.totient 185615900804143121119283771297 = 175846544180122810596732925200 := by
  rw [← show ((([(19, 1), (1781863, 1), (5482608897014060154701, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_19, prime_oneHundredFiftySevenEY_1781863, prime_oneHundredFiftySevenEY_5482608897014060154701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771298 : Nat.totient 185615900804143121119283771298 = 61871946343423141257125862912 := by
  rw [← show ((([(2, 1), (3, 3), (3005329, 1), (24074106059, 1), (47509365017, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_3005329, prime_oneHundredFiftySevenEY_24074106059, prime_oneHundredFiftySevenEY_47509365017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771299 : Nat.totient 185615900804143121119283771299 = 182748043622261289230039798784 := by
  rw [← show ((([(139, 1), (149, 1), (619, 1), (2649842383, 1), (5463908494817, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_139, prime_oneHundredFiftySevenEY_149, prime_oneHundredFiftySevenEY_619, prime_oneHundredFiftySevenEY_2649842383, prime_oneHundredFiftySevenEY_5463908494817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771300 : Nat.totient 185615900804143121119283771300 = 74246265560958246265898880000 := by
  rw [← show ((([(2, 2), (5, 2), (881743, 1), (7033151, 1), (299311370204641, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_2, prime_oneHundredFiftySevenEY_5, prime_oneHundredFiftySevenEY_881743, prime_oneHundredFiftySevenEY_7033151, prime_oneHundredFiftySevenEY_299311370204641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySevenEY_185615900804143121119283771301 : Nat.totient 185615900804143121119283771301 = 122596276542411649685838137280 := by
  rw [← show ((([(3, 1), (109, 1), (9907, 1), (7703011, 1), (7438146770479819, 1)] : List FactorBlock).map factorBlockValue).prod) = 185615900804143121119283771301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySevenEY_3, prime_oneHundredFiftySevenEY_109, prime_oneHundredFiftySevenEY_9907, prime_oneHundredFiftySevenEY_7703011, prime_oneHundredFiftySevenEY_7438146770479819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftySevenEY : certifiedKill 1 185615900804143121119283771199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftySevenEY_185615900804143121119283771200, phi_oneHundredFiftySevenEY_185615900804143121119283771201, phi_oneHundredFiftySevenEY_185615900804143121119283771202,
    phi_oneHundredFiftySevenEY_185615900804143121119283771203, phi_oneHundredFiftySevenEY_185615900804143121119283771204, phi_oneHundredFiftySevenEY_185615900804143121119283771205,
    phi_oneHundredFiftySevenEY_185615900804143121119283771206, phi_oneHundredFiftySevenEY_185615900804143121119283771207, phi_oneHundredFiftySevenEY_185615900804143121119283771208,
    phi_oneHundredFiftySevenEY_185615900804143121119283771209, phi_oneHundredFiftySevenEY_185615900804143121119283771210, phi_oneHundredFiftySevenEY_185615900804143121119283771211,
    phi_oneHundredFiftySevenEY_185615900804143121119283771212, phi_oneHundredFiftySevenEY_185615900804143121119283771213, phi_oneHundredFiftySevenEY_185615900804143121119283771214,
    phi_oneHundredFiftySevenEY_185615900804143121119283771215, phi_oneHundredFiftySevenEY_185615900804143121119283771216, phi_oneHundredFiftySevenEY_185615900804143121119283771217,
    phi_oneHundredFiftySevenEY_185615900804143121119283771218, phi_oneHundredFiftySevenEY_185615900804143121119283771219, phi_oneHundredFiftySevenEY_185615900804143121119283771220,
    phi_oneHundredFiftySevenEY_185615900804143121119283771221, phi_oneHundredFiftySevenEY_185615900804143121119283771222, phi_oneHundredFiftySevenEY_185615900804143121119283771223,
    phi_oneHundredFiftySevenEY_185615900804143121119283771224, phi_oneHundredFiftySevenEY_185615900804143121119283771225, phi_oneHundredFiftySevenEY_185615900804143121119283771226,
    phi_oneHundredFiftySevenEY_185615900804143121119283771227, phi_oneHundredFiftySevenEY_185615900804143121119283771228, phi_oneHundredFiftySevenEY_185615900804143121119283771229,
    phi_oneHundredFiftySevenEY_185615900804143121119283771230, phi_oneHundredFiftySevenEY_185615900804143121119283771231, phi_oneHundredFiftySevenEY_185615900804143121119283771232,
    phi_oneHundredFiftySevenEY_185615900804143121119283771233, phi_oneHundredFiftySevenEY_185615900804143121119283771234, phi_oneHundredFiftySevenEY_185615900804143121119283771235,
    phi_oneHundredFiftySevenEY_185615900804143121119283771236, phi_oneHundredFiftySevenEY_185615900804143121119283771237, phi_oneHundredFiftySevenEY_185615900804143121119283771238,
    phi_oneHundredFiftySevenEY_185615900804143121119283771239, phi_oneHundredFiftySevenEY_185615900804143121119283771240, phi_oneHundredFiftySevenEY_185615900804143121119283771241,
    phi_oneHundredFiftySevenEY_185615900804143121119283771242, phi_oneHundredFiftySevenEY_185615900804143121119283771243, phi_oneHundredFiftySevenEY_185615900804143121119283771244,
    phi_oneHundredFiftySevenEY_185615900804143121119283771245, phi_oneHundredFiftySevenEY_185615900804143121119283771246, phi_oneHundredFiftySevenEY_185615900804143121119283771247,
    phi_oneHundredFiftySevenEY_185615900804143121119283771248, phi_oneHundredFiftySevenEY_185615900804143121119283771249, phi_oneHundredFiftySevenEY_185615900804143121119283771250,
    phi_oneHundredFiftySevenEY_185615900804143121119283771251, phi_oneHundredFiftySevenEY_185615900804143121119283771252, phi_oneHundredFiftySevenEY_185615900804143121119283771253,
    phi_oneHundredFiftySevenEY_185615900804143121119283771254, phi_oneHundredFiftySevenEY_185615900804143121119283771255, phi_oneHundredFiftySevenEY_185615900804143121119283771256,
    phi_oneHundredFiftySevenEY_185615900804143121119283771257, phi_oneHundredFiftySevenEY_185615900804143121119283771258, phi_oneHundredFiftySevenEY_185615900804143121119283771259,
    phi_oneHundredFiftySevenEY_185615900804143121119283771260, phi_oneHundredFiftySevenEY_185615900804143121119283771261, phi_oneHundredFiftySevenEY_185615900804143121119283771262,
    phi_oneHundredFiftySevenEY_185615900804143121119283771263, phi_oneHundredFiftySevenEY_185615900804143121119283771264, phi_oneHundredFiftySevenEY_185615900804143121119283771265,
    phi_oneHundredFiftySevenEY_185615900804143121119283771266, phi_oneHundredFiftySevenEY_185615900804143121119283771267, phi_oneHundredFiftySevenEY_185615900804143121119283771268,
    phi_oneHundredFiftySevenEY_185615900804143121119283771269, phi_oneHundredFiftySevenEY_185615900804143121119283771270, phi_oneHundredFiftySevenEY_185615900804143121119283771271,
    phi_oneHundredFiftySevenEY_185615900804143121119283771272, phi_oneHundredFiftySevenEY_185615900804143121119283771273, phi_oneHundredFiftySevenEY_185615900804143121119283771274,
    phi_oneHundredFiftySevenEY_185615900804143121119283771275, phi_oneHundredFiftySevenEY_185615900804143121119283771276, phi_oneHundredFiftySevenEY_185615900804143121119283771277,
    phi_oneHundredFiftySevenEY_185615900804143121119283771278, phi_oneHundredFiftySevenEY_185615900804143121119283771279, phi_oneHundredFiftySevenEY_185615900804143121119283771280,
    phi_oneHundredFiftySevenEY_185615900804143121119283771281, phi_oneHundredFiftySevenEY_185615900804143121119283771282, phi_oneHundredFiftySevenEY_185615900804143121119283771283,
    phi_oneHundredFiftySevenEY_185615900804143121119283771284, phi_oneHundredFiftySevenEY_185615900804143121119283771285, phi_oneHundredFiftySevenEY_185615900804143121119283771286,
    phi_oneHundredFiftySevenEY_185615900804143121119283771287, phi_oneHundredFiftySevenEY_185615900804143121119283771288, phi_oneHundredFiftySevenEY_185615900804143121119283771289,
    phi_oneHundredFiftySevenEY_185615900804143121119283771290, phi_oneHundredFiftySevenEY_185615900804143121119283771291, phi_oneHundredFiftySevenEY_185615900804143121119283771292,
    phi_oneHundredFiftySevenEY_185615900804143121119283771293, phi_oneHundredFiftySevenEY_185615900804143121119283771294, phi_oneHundredFiftySevenEY_185615900804143121119283771295,
    phi_oneHundredFiftySevenEY_185615900804143121119283771296, phi_oneHundredFiftySevenEY_185615900804143121119283771297, phi_oneHundredFiftySevenEY_185615900804143121119283771298,
    phi_oneHundredFiftySevenEY_185615900804143121119283771299, phi_oneHundredFiftySevenEY_185615900804143121119283771300, phi_oneHundredFiftySevenEY_185615900804143121119283771301
    ]

end TotientTailPeriodKiller
end Erdos249257

