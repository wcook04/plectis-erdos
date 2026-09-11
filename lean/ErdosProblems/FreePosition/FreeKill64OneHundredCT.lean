import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredCTFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredCTFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredCTFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredCTFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredCTFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredCTFastPow a n * oneHundredCTFastPow a n * a else oneHundredCTFastPow a n * oneHundredCTFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredCT_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredCT_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredCT_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredCT_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredCT_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredCT_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredCT_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredCT_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredCT_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredCT_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredCT_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredCT_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredCT_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredCT_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredCT_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredCT_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredCT_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredCT_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredCT_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredCT_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredCT_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredCT_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredCT_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredCT_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredCT_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredCT_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredCT_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredCT_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredCT_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredCT_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredCT_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredCT_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredCT_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredCT_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredCT_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredCT_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredCT_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredCT_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredCT_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredCT_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredCT_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredCT_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredCT_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredCT_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredCT_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredCT_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredCT_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredCT_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredCT_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredCT_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredCT_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredCT_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredCT_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredCT_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredCT_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredCT_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredCT_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredCT_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredCT_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredCT_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredCT_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredCT_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredCT_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredCT_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredCT_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredCT_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredCT_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredCT_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredCT_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredCT_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredCT_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredCT_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredCT_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredCT_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredCT_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredCT_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredCT_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredCT_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredCT_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredCT_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredCT_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredCT_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredCT_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredCT_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredCT_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredCT_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredCT_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredCT_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredCT_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredCT_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredCT_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredCT_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredCT_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredCT_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredCT_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredCT_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredCT_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredCT_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredCT_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredCT_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredCT_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredCT_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredCT_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredCT_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredCT_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredCT_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredCT_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredCT_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredCT_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredCT_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredCT_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredCT_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredCT_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredCT_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredCT_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredCT_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredCT_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredCT_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredCT_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredCT_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredCT_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredCT_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredCT_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredCT_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredCT_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredCT_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredCT_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredCT_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredCT_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredCT_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredCT_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredCT_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredCT_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_oneHundredCT_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredCT_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredCT_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredCT_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredCT_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredCT_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_oneHundredCT_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredCT_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredCT_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredCT_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredCT_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredCT_3187 : Nat.Prime 3187 := by norm_num

private theorem prime_oneHundredCT_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredCT_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredCT_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_oneHundredCT_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredCT_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredCT_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredCT_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredCT_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredCT_3853 : Nat.Prime 3853 := by norm_num

private theorem prime_oneHundredCT_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredCT_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_oneHundredCT_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_oneHundredCT_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredCT_4177 : Nat.Prime 4177 := by norm_num

private theorem prime_oneHundredCT_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredCT_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredCT_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredCT_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_oneHundredCT_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredCT_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_oneHundredCT_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_oneHundredCT_5503 : Nat.Prime 5503 := by norm_num

private theorem prime_oneHundredCT_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_oneHundredCT_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredCT_5953 : Nat.Prime 5953 := by norm_num

private theorem prime_oneHundredCT_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_oneHundredCT_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_oneHundredCT_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_oneHundredCT_6469 : Nat.Prime 6469 := by norm_num

private theorem prime_oneHundredCT_6481 : Nat.Prime 6481 := by norm_num

private theorem prime_oneHundredCT_6779 : Nat.Prime 6779 := by norm_num

private theorem prime_oneHundredCT_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredCT_7019 : Nat.Prime 7019 := by norm_num

private theorem prime_oneHundredCT_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredCT_7603 : Nat.Prime 7603 := by norm_num

private theorem prime_oneHundredCT_7681 : Nat.Prime 7681 := by norm_num

private theorem prime_oneHundredCT_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredCT_8287 : Nat.Prime 8287 := by norm_num

private theorem prime_oneHundredCT_8719 : Nat.Prime 8719 := by norm_num

private theorem prime_oneHundredCT_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_oneHundredCT_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredCT_9371 : Nat.Prime 9371 := by norm_num

private theorem prime_oneHundredCT_9871 : Nat.Prime 9871 := by norm_num

private theorem prime_oneHundredCT_9907 : Nat.Prime 9907 := by norm_num

private theorem prime_oneHundredCT_10133 : Nat.Prime 10133 := by norm_num

private theorem prime_oneHundredCT_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredCT_11059 : Nat.Prime 11059 := by norm_num

private theorem prime_oneHundredCT_11069 : Nat.Prime 11069 := by norm_num

private theorem prime_oneHundredCT_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_oneHundredCT_11329 : Nat.Prime 11329 := by norm_num

private theorem prime_oneHundredCT_11497 : Nat.Prime 11497 := by norm_num

private theorem prime_oneHundredCT_11551 : Nat.Prime 11551 := by norm_num

private theorem prime_oneHundredCT_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredCT_11813 : Nat.Prime 11813 := by norm_num

private theorem prime_oneHundredCT_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredCT_12757 : Nat.Prime 12757 := by norm_num

private theorem prime_oneHundredCT_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_oneHundredCT_13711 : Nat.Prime 13711 := by norm_num

private theorem prime_oneHundredCT_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_oneHundredCT_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredCT_14683 : Nat.Prime 14683 := by norm_num

private theorem prime_oneHundredCT_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_oneHundredCT_14887 : Nat.Prime 14887 := by norm_num

private theorem prime_oneHundredCT_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredCT_15683 : Nat.Prime 15683 := by norm_num

private theorem prime_oneHundredCT_15971 : Nat.Prime 15971 := by norm_num

private theorem prime_oneHundredCT_16349 : Nat.Prime 16349 := by norm_num

private theorem prime_oneHundredCT_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredCT_17351 : Nat.Prime 17351 := by norm_num

private theorem prime_oneHundredCT_18229 : Nat.Prime 18229 := by norm_num

private theorem prime_oneHundredCT_19013 : Nat.Prime 19013 := by norm_num

private theorem prime_oneHundredCT_19319 : Nat.Prime 19319 := by norm_num

private theorem prime_oneHundredCT_19489 : Nat.Prime 19489 := by norm_num

private theorem prime_oneHundredCT_20117 : Nat.Prime 20117 := by norm_num

private theorem prime_oneHundredCT_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredCT_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredCT_21221 : Nat.Prime 21221 := by norm_num

private theorem prime_oneHundredCT_21911 : Nat.Prime 21911 := by norm_num

private theorem prime_oneHundredCT_22381 : Nat.Prime 22381 := by norm_num

private theorem prime_oneHundredCT_22567 : Nat.Prime 22567 := by norm_num

private theorem prime_oneHundredCT_22943 : Nat.Prime 22943 := by norm_num

private theorem prime_oneHundredCT_23227 : Nat.Prime 23227 := by norm_num

private theorem prime_oneHundredCT_24137 : Nat.Prime 24137 := by norm_num

private theorem prime_oneHundredCT_25471 : Nat.Prime 25471 := by norm_num

private theorem prime_oneHundredCT_26591 : Nat.Prime 26591 := by norm_num

private theorem prime_oneHundredCT_26701 : Nat.Prime 26701 := by norm_num

private theorem prime_oneHundredCT_26893 : Nat.Prime 26893 := by norm_num

private theorem prime_oneHundredCT_27529 : Nat.Prime 27529 := by norm_num

private theorem prime_oneHundredCT_27539 : Nat.Prime 27539 := by norm_num

private theorem prime_oneHundredCT_28541 : Nat.Prime 28541 := by norm_num

private theorem prime_oneHundredCT_29473 : Nat.Prime 29473 := by norm_num

private theorem prime_oneHundredCT_30097 : Nat.Prime 30097 := by norm_num

private theorem prime_oneHundredCT_30493 : Nat.Prime 30493 := by norm_num

private theorem prime_oneHundredCT_31307 : Nat.Prime 31307 := by norm_num

private theorem prime_oneHundredCT_31337 : Nat.Prime 31337 := by norm_num

private theorem prime_oneHundredCT_31567 : Nat.Prime 31567 := by norm_num

private theorem prime_oneHundredCT_32069 : Nat.Prime 32069 := by norm_num

private theorem prime_oneHundredCT_33757 : Nat.Prime 33757 := by norm_num

private theorem prime_oneHundredCT_33827 : Nat.Prime 33827 := by norm_num

private theorem prime_oneHundredCT_35069 : Nat.Prime 35069 := by norm_num

private theorem prime_oneHundredCT_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredCT_39341 : Nat.Prime 39341 := by norm_num

private theorem prime_oneHundredCT_39451 : Nat.Prime 39451 := by norm_num

private theorem prime_oneHundredCT_40151 : Nat.Prime 40151 := by norm_num

private theorem prime_oneHundredCT_41777 : Nat.Prime 41777 := by norm_num

private theorem prime_oneHundredCT_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredCT_48121 : Nat.Prime 48121 := by norm_num

private theorem prime_oneHundredCT_49499 : Nat.Prime 49499 := by norm_num

private theorem prime_oneHundredCT_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredCT_51749 : Nat.Prime 51749 := by norm_num

private theorem prime_oneHundredCT_52457 : Nat.Prime 52457 := by norm_num

private theorem prime_oneHundredCT_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredCT_54449 : Nat.Prime 54449 := by norm_num

private theorem prime_oneHundredCT_55339 : Nat.Prime 55339 := by norm_num

private theorem prime_oneHundredCT_56237 : Nat.Prime 56237 := by norm_num

private theorem prime_oneHundredCT_56503 : Nat.Prime 56503 := by norm_num

private theorem prime_oneHundredCT_56687 : Nat.Prime 56687 := by norm_num

private theorem prime_oneHundredCT_56893 : Nat.Prime 56893 := by norm_num

private theorem prime_oneHundredCT_60083 : Nat.Prime 60083 := by norm_num

private theorem prime_oneHundredCT_61043 : Nat.Prime 61043 := by norm_num

private theorem prime_oneHundredCT_62303 : Nat.Prime 62303 := by norm_num

private theorem prime_oneHundredCT_62467 : Nat.Prime 62467 := by norm_num

private theorem prime_oneHundredCT_63907 : Nat.Prime 63907 := by norm_num

private theorem prime_oneHundredCT_65437 : Nat.Prime 65437 := by norm_num

private theorem prime_oneHundredCT_69557 : Nat.Prime 69557 := by norm_num

private theorem prime_oneHundredCT_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredCT_71191 : Nat.Prime 71191 := by norm_num

private theorem prime_oneHundredCT_72467 : Nat.Prime 72467 := by norm_num

private theorem prime_oneHundredCT_77041 : Nat.Prime 77041 := by norm_num

private theorem prime_oneHundredCT_81233 : Nat.Prime 81233 := by norm_num

private theorem prime_oneHundredCT_83903 : Nat.Prime 83903 := by norm_num

private theorem prime_oneHundredCT_84443 : Nat.Prime 84443 := by norm_num

private theorem prime_oneHundredCT_89399 : Nat.Prime 89399 := by norm_num

private theorem prime_oneHundredCT_90173 : Nat.Prime 90173 := by norm_num

private theorem prime_oneHundredCT_95191 : Nat.Prime 95191 := by norm_num

private theorem prime_oneHundredCT_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredCT_105277 : Nat.Prime 105277 := by norm_num

private theorem prime_oneHundredCT_106753 : Nat.Prime 106753 := by norm_num

private theorem prime_oneHundredCT_109111 : Nat.Prime 109111 := by norm_num

private theorem prime_oneHundredCT_113143 : Nat.Prime 113143 := by norm_num

private theorem prime_oneHundredCT_115883 : Nat.Prime 115883 := by norm_num

private theorem prime_oneHundredCT_130211 : Nat.Prime 130211 := by norm_num

private theorem prime_oneHundredCT_132533 : Nat.Prime 132533 := by norm_num

private theorem prime_oneHundredCT_140053 : Nat.Prime 140053 := by norm_num

private theorem prime_oneHundredCT_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredCT_165463 : Nat.Prime 165463 := by norm_num

private theorem prime_oneHundredCT_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredCT_179969 : Nat.Prime 179969 := by norm_num

private theorem prime_oneHundredCT_181459 : Nat.Prime 181459 := by norm_num

private theorem prime_oneHundredCT_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredCT_195253 : Nat.Prime 195253 := by norm_num

private theorem prime_oneHundredCT_203417 : Nat.Prime 203417 := by norm_num

private theorem prime_oneHundredCT_219979 : Nat.Prime 219979 := by norm_num

private theorem prime_oneHundredCT_225223 : Nat.Prime 225223 := by norm_num

private theorem prime_oneHundredCT_235397 : Nat.Prime 235397 := by norm_num

private theorem prime_oneHundredCT_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredCT_251917 : Nat.Prime 251917 := by norm_num

private theorem prime_oneHundredCT_253543 : Nat.Prime 253543 := by norm_num

private theorem prime_oneHundredCT_256121 : Nat.Prime 256121 := by norm_num

private theorem prime_oneHundredCT_264601 : Nat.Prime 264601 := by norm_num

private theorem prime_oneHundredCT_264757 : Nat.Prime 264757 := by norm_num

private theorem prime_oneHundredCT_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredCT_280711 : Nat.Prime 280711 := by norm_num

private theorem prime_oneHundredCT_284777 : Nat.Prime 284777 := by norm_num

private theorem prime_oneHundredCT_291721 : Nat.Prime 291721 := by norm_num

private theorem prime_oneHundredCT_335633 : Nat.Prime 335633 := by norm_num

private theorem prime_oneHundredCT_351031 : Nat.Prime 351031 := by norm_num

private theorem prime_oneHundredCT_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredCT_368857 : Nat.Prime 368857 := by norm_num

private theorem prime_oneHundredCT_390781 : Nat.Prime 390781 := by norm_num

private theorem prime_oneHundredCT_401311 : Nat.Prime 401311 := by norm_num

private theorem prime_oneHundredCT_403289 : Nat.Prime 403289 := by norm_num

private theorem prime_oneHundredCT_447211 : Nat.Prime 447211 := by norm_num

private theorem prime_oneHundredCT_485137 : Nat.Prime 485137 := by norm_num

private theorem prime_oneHundredCT_492871 : Nat.Prime 492871 := by norm_num

private theorem prime_oneHundredCT_586741 : Nat.Prime 586741 := by norm_num

private theorem prime_oneHundredCT_588827 : Nat.Prime 588827 := by norm_num

private theorem prime_oneHundredCT_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredCT_700307 : Nat.Prime 700307 := by norm_num

private theorem prime_oneHundredCT_700643 : Nat.Prime 700643 := by norm_num

private theorem prime_oneHundredCT_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredCT_723133 : Nat.Prime 723133 := by norm_num

private theorem prime_oneHundredCT_743173 : Nat.Prime 743173 := by norm_num

private theorem prime_oneHundredCT_744859 : Nat.Prime 744859 := by norm_num

private theorem prime_oneHundredCT_750983 : Nat.Prime 750983 := by norm_num

private theorem prime_oneHundredCT_755239 : Nat.Prime 755239 := by norm_num

private theorem prime_oneHundredCT_771643 : Nat.Prime 771643 := by norm_num

private theorem prime_oneHundredCT_862441 : Nat.Prime 862441 := by norm_num

private theorem prime_oneHundredCT_963871 : Nat.Prime 963871 := by norm_num

private theorem prime_oneHundredCT_970259 : Nat.Prime 970259 := by norm_num

private theorem prime_oneHundredCT_1024589 : Nat.Prime 1024589 := by norm_num

private theorem prime_oneHundredCT_1031431 : Nat.Prime 1031431 := by norm_num

private theorem prime_oneHundredCT_1045123 : Nat.Prime 1045123 := by norm_num

private theorem prime_oneHundredCT_1090151 : Nat.Prime 1090151 := by norm_num

private theorem prime_oneHundredCT_1104739 : Nat.Prime 1104739 := by norm_num

private theorem prime_oneHundredCT_1144993 : Nat.Prime 1144993 := by norm_num

private theorem prime_oneHundredCT_1150547 : Nat.Prime 1150547 := by norm_num

private theorem prime_oneHundredCT_1166723 : Nat.Prime 1166723 := by norm_num

private theorem prime_oneHundredCT_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredCT_1251323 : Nat.Prime 1251323 := by norm_num

private theorem prime_oneHundredCT_1260341 : Nat.Prime 1260341 := by norm_num

private theorem prime_oneHundredCT_1300051 : Nat.Prime 1300051 := by norm_num

private theorem prime_oneHundredCT_1324511 : Nat.Prime 1324511 := by norm_num

private theorem prime_oneHundredCT_1329971 : Nat.Prime 1329971 := by norm_num

private theorem prime_oneHundredCT_1375981 : Nat.Prime 1375981 := by norm_num

private theorem prime_oneHundredCT_1419233 : Nat.Prime 1419233 := by norm_num

private theorem prime_oneHundredCT_1524007 : Nat.Prime 1524007 := by norm_num

private theorem prime_oneHundredCT_1784683 : Nat.Prime 1784683 := by norm_num

private theorem prime_oneHundredCT_1896883 : Nat.Prime 1896883 := by norm_num

private theorem prime_oneHundredCT_1931051 : Nat.Prime 1931051 := by norm_num

private theorem prime_oneHundredCT_1980817 : Nat.Prime 1980817 := by norm_num

private theorem prime_oneHundredCT_2174941 : Nat.Prime 2174941 := by norm_num

private theorem prime_oneHundredCT_2230759 : Nat.Prime 2230759 := by norm_num

private theorem prime_oneHundredCT_2252623 : Nat.Prime 2252623 := by norm_num

private theorem prime_oneHundredCT_2276699 : Nat.Prime 2276699 := by norm_num

private theorem prime_oneHundredCT_2347153 : Nat.Prime 2347153 := by norm_num

private theorem prime_oneHundredCT_2409203 : Nat.Prime 2409203 := by norm_num

private theorem prime_oneHundredCT_2500999 : Nat.Prime 2500999 := by norm_num

private theorem prime_oneHundredCT_2688467 : Nat.Prime 2688467 := by norm_num

private theorem prime_oneHundredCT_2823971 : Nat.Prime 2823971 := by norm_num

private theorem prime_oneHundredCT_2834047 : Nat.Prime 2834047 := by norm_num

private theorem prime_oneHundredCT_2915699 : Nat.Prime 2915699 := by norm_num

private theorem prime_oneHundredCT_3009781 : Nat.Prime 3009781 := by norm_num

private theorem prime_oneHundredCT_3050023 : Nat.Prime 3050023 := by norm_num

private theorem prime_oneHundredCT_3090781 : Nat.Prime 3090781 := by norm_num

private theorem prime_oneHundredCT_3441829 : Nat.Prime 3441829 := by norm_num

private theorem prime_oneHundredCT_3586907 : Nat.Prime 3586907 := by norm_num

private theorem prime_oneHundredCT_3591073 : Nat.Prime 3591073 := by norm_num

private theorem prime_oneHundredCT_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredCT_3710683 : Nat.Prime 3710683 := by norm_num

private theorem prime_oneHundredCT_3756097 : Nat.Prime 3756097 := by norm_num

private theorem prime_oneHundredCT_3869501 : Nat.Prime 3869501 := by norm_num

private theorem prime_oneHundredCT_3962759 : Nat.Prime 3962759 := by norm_num

private theorem prime_oneHundredCT_3993889 : Nat.Prime 3993889 := by norm_num

private theorem prime_oneHundredCT_4382429 : Nat.Prime 4382429 := by norm_num

private theorem prime_oneHundredCT_4671137 : Nat.Prime 4671137 := by norm_num

private theorem prime_oneHundredCT_4674151 : Nat.Prime 4674151 := by norm_num

private theorem prime_oneHundredCT_4893853 : Nat.Prime 4893853 := by norm_num

private theorem prime_oneHundredCT_5230997 : Nat.Prime 5230997 := by norm_num

private theorem prime_oneHundredCT_5246713 : Nat.Prime 5246713 := by norm_num

private theorem prime_oneHundredCT_5544911 : Nat.Prime 5544911 := by norm_num

private theorem prime_oneHundredCT_5863469 : Nat.Prime 5863469 := by norm_num

private theorem prime_oneHundredCT_6039659 : Nat.Prime 6039659 := by norm_num

private theorem prime_oneHundredCT_6380281 : Nat.Prime 6380281 := by norm_num

private theorem prime_oneHundredCT_6496339 : Nat.Prime 6496339 := by norm_num

private theorem prime_oneHundredCT_6697657 : Nat.Prime 6697657 := by norm_num

private theorem prime_oneHundredCT_6703889 : Nat.Prime 6703889 := by norm_num

private theorem prime_oneHundredCT_6902633 : Nat.Prime 6902633 := by norm_num

private theorem prime_oneHundredCT_7695671 : Nat.Prime 7695671 := by norm_num

private theorem prime_oneHundredCT_8487079 : Nat.Prime 8487079 := by norm_num

private theorem prime_oneHundredCT_8837137 : Nat.Prime 8837137 := by norm_num

private theorem prime_oneHundredCT_9157949 : Nat.Prime 9157949 := by norm_num

private theorem prime_oneHundredCT_9407971 : Nat.Prime 9407971 := by norm_num

private theorem prime_oneHundredCT_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredCT_9652453 : Nat.Prime 9652453 := by norm_num

private theorem prime_oneHundredCT_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredCT_11292583 : Nat.Prime 11292583 := by norm_num

private theorem prime_oneHundredCT_11333351 : Nat.Prime 11333351 := by norm_num

private theorem prime_oneHundredCT_11940857 : Nat.Prime 11940857 := by norm_num

private theorem prime_oneHundredCT_12844297 : Nat.Prime 12844297 := by norm_num

private theorem prime_oneHundredCT_13151923 : Nat.Prime 13151923 := by norm_num

private theorem prime_oneHundredCT_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredCT_14483401 : Nat.Prime 14483401 := by norm_num

private theorem prime_oneHundredCT_18124331 : Nat.Prime 18124331 := by norm_num

private theorem prime_oneHundredCT_18151967 : Nat.Prime 18151967 := by norm_num

private theorem prime_oneHundredCT_19067063 : Nat.Prime 19067063 := by norm_num

private theorem prime_oneHundredCT_19384979 : Nat.Prime 19384979 := by norm_num

private theorem prime_oneHundredCT_19878623 : Nat.Prime 19878623 := by norm_num

private theorem prime_oneHundredCT_20047151 : Nat.Prime 20047151 := by norm_num

private theorem prime_oneHundredCT_20261191 : Nat.Prime 20261191 := by norm_num

private theorem prime_oneHundredCT_20681891 : Nat.Prime 20681891 := by norm_num

private theorem prime_oneHundredCT_20901469 : Nat.Prime 20901469 := by norm_num

private theorem prime_oneHundredCT_21220153 : Nat.Prime 21220153 := by norm_num

private theorem prime_oneHundredCT_22377391 : Nat.Prime 22377391 := by norm_num

private theorem prime_oneHundredCT_22512661 : Nat.Prime 22512661 := by norm_num

private theorem prime_oneHundredCT_22998923 : Nat.Prime 22998923 := by norm_num

private theorem prime_oneHundredCT_24205387 : Nat.Prime 24205387 := by norm_num

private theorem prime_oneHundredCT_26198603 : Nat.Prime 26198603 := by norm_num

private theorem prime_oneHundredCT_28506437 : Nat.Prime 28506437 := by norm_num

private theorem prime_oneHundredCT_29701037 : Nat.Prime 29701037 := by norm_num

private theorem prime_oneHundredCT_35059433 : Nat.Prime 35059433 := by
  apply lucas_primality 35059433 (3 : ZMod 35059433)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4382429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4382429, 1)] : List FactorBlock).map factorBlockValue).prod) = 35059433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_4382429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 35059433) ^ 17529716 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 35059433) ^ 8 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_36401429 : Nat.Prime 36401429 := by
  apply lucas_primality 36401429 (2 : ZMod 36401429)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1300051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1300051, 1)] : List FactorBlock).map factorBlockValue).prod) = 36401429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_1300051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36401429) ^ 18200714 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 36401429) ^ 5200204 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 36401429) ^ 28 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_37561127 : Nat.Prime 37561127 := by
  apply lucas_primality 37561127 (5 : ZMod 37561127)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1104739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1104739, 1)] : List FactorBlock).map factorBlockValue).prod) = 37561127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_1104739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37561127) ^ 18780563 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37561127) ^ 2209478 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37561127) ^ 34 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_38134127 : Nat.Prime 38134127 := by
  apply lucas_primality 38134127 (5 : ZMod 38134127)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19067063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19067063, 1)] : List FactorBlock).map factorBlockValue).prod) = 38134127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19067063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 38134127) ^ 19067063 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 38134127) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_39602887 : Nat.Prime 39602887 := by
  apply lucas_primality 39602887 (3 : ZMod 39602887)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1061, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1061, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) = 39602887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1061
      · exact prime_oneHundredCT_6221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39602887) ^ 19801443 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 39602887) ^ 13200962 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 39602887) ^ 37326 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 39602887) ^ 6366 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_41325241 : Nat.Prime 41325241 := by
  apply lucas_primality 41325241 (21 : ZMod 41325241)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (31307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (31307, 1)] : List FactorBlock).map factorBlockValue).prod) = 41325241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_31307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 41325241) ^ 20662620 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (21 : ZMod 41325241) ^ 13775080 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (21 : ZMod 41325241) ^ 8265048 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (21 : ZMod 41325241) ^ 3756840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (21 : ZMod 41325241) ^ 1320 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_43092877 : Nat.Prime 43092877 := by
  apply lucas_primality 43092877 (2 : ZMod 43092877)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) = 43092877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_3591073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43092877) ^ 21546438 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 14364292 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 12 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_44016979 : Nat.Prime 44016979 := by
  apply lucas_primality 44016979 (2 : ZMod 44016979)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (397, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (397, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 44016979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_397
      · exact prime_oneHundredCT_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44016979) ^ 22008489 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 14672326 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 2589234 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 110874 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44016979) ^ 40494 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_46174027 : Nat.Prime 46174027 := by
  apply lucas_primality 46174027 (2 : ZMod 46174027)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) = 46174027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7695671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46174027) ^ 23087013 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 15391342 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 6 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_46475983 : Nat.Prime 46475983 := by
  apply lucas_primality 46475983 (3 : ZMod 46475983)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (368857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (368857, 1)] : List FactorBlock).map factorBlockValue).prod) = 46475983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_368857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46475983) ^ 23237991 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46475983) ^ 15491994 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46475983) ^ 6639426 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46475983) ^ 126 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_46484761 : Nat.Prime 46484761 := by
  apply lucas_primality 46484761 (26 : ZMod 46484761)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (55339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (55339, 1)] : List FactorBlock).map factorBlockValue).prod) = 46484761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_55339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 46484761) ^ 23242380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 15494920 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 9296952 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 6640680 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_41
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_50027641 : Nat.Prime 50027641 := by
  apply lucas_primality 50027641 (14 : ZMod 50027641)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod) = 50027641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_32069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 50027641) ^ 25013820 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 16675880 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 10005528 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 3848280 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 1560 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_50694841 : Nat.Prime 50694841 := by
  apply lucas_primality 50694841 (11 : ZMod 50694841)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (20117, 1)] : List FactorBlock).map factorBlockValue).prod) = 50694841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_20117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 50694841) ^ 25347420 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 50694841) ^ 16898280 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 50694841) ^ 10138968 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 50694841) ^ 7242120 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 50694841) ^ 2520 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_51923327 : Nat.Prime 51923327 := by
  apply lucas_primality 51923327 (7 : ZMod 51923327)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_9203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51923327) ^ 25961663 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 7417618 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 3994102 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 1674946 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 5642 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_54605701 : Nat.Prime 54605701 := by
  apply lucas_primality 54605701 (2 : ZMod 54605701)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (17, 1), (43, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (17, 1), (43, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 54605701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54605701) ^ 27302850 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54605701) ^ 18201900 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54605701) ^ 10921140 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54605701) ^ 3212100 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54605701) ^ 1269900 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 54605701) ^ 657900 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_55413389 : Nat.Prime 55413389 := by
  apply lucas_primality 55413389 (2 : ZMod 55413389)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55413389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_179
      · exact prime_oneHundredCT_193
      · exact prime_oneHundredCT_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55413389) ^ 27706694 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 309572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 287116 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 138188 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_56511551 : Nat.Prime 56511551 := by
  apply lucas_primality 56511551 (26 : ZMod 56511551)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (239, 1), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (239, 1), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) = 56511551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_239
      · exact prime_oneHundredCT_4729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 56511551) ^ 28255775 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 56511551) ^ 11302310 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 56511551) ^ 236450 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (26 : ZMod 56511551) ^ 11950 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_1811
      · exact prime_oneHundredCT_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_67997183 : Nat.Prime 67997183 := by
  apply lucas_primality 67997183 (5 : ZMod 67997183)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3090781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3090781, 1)] : List FactorBlock).map factorBlockValue).prod) = 67997183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_3090781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67997183) ^ 33998591 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 67997183) ^ 6181562 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 67997183) ^ 22 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_69313553 : Nat.Prime 69313553 := by
  apply lucas_primality 69313553 (3 : ZMod 69313553)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (127, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (127, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 69313553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_127
      · exact prime_oneHundredCT_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69313553) ^ 34656776 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 69313553) ^ 9901936 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 69313553) ^ 6301232 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 69313553) ^ 545776 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 69313553) ^ 156464 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_77599139 : Nat.Prime 77599139 := by
  apply lucas_primality 77599139 (2 : ZMod 77599139)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (33827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (33827, 1)] : List FactorBlock).map factorBlockValue).prod) = 77599139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_33827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77599139) ^ 38799569 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2503198 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2097274 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77599139) ^ 2294 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_82829821 : Nat.Prime 82829821 := by
  apply lucas_primality 82829821 (2 : ZMod 82829821)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 82829821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_601
      · exact prime_oneHundredCT_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82829821) ^ 41414910 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 27609940 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 16565964 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 137820 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 36060 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_84360119 : Nat.Prime 84360119 := by
  apply lucas_primality 84360119 (7 : ZMod 84360119)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (397, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (397, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 84360119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_181
      · exact prime_oneHundredCT_397
      · exact prime_oneHundredCT_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 84360119) ^ 42180059 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 84360119) ^ 466078 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 84360119) ^ 212494 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 84360119) ^ 143714 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_89111779 : Nat.Prime 89111779 := by
  apply lucas_primality 89111779 (2 : ZMod 89111779)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (51749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (51749, 1)] : List FactorBlock).map factorBlockValue).prod) = 89111779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_41
      · exact prime_oneHundredCT_51749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89111779) ^ 44555889 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 29703926 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 12730254 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 2173458 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 89111779) ^ 1722 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_90131191 : Nat.Prime 90131191 := by
  apply lucas_primality 90131191 (13 : ZMod 90131191)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) = 90131191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_89
      · exact prime_oneHundredCT_33757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 90131191) ^ 45065595 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 30043730 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 18026238 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 1012710 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 2670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_92889289 : Nat.Prime 92889289 := by
  apply lucas_primality 92889289 (7 : ZMod 92889289)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (43, 1), (73, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (43, 1), (73, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 92889289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 92889289) ^ 46444644 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 92889289) ^ 30963096 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 92889289) ^ 2160216 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 92889289) ^ 1272456 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 92889289) ^ 678024 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_102406289 : Nat.Prime 102406289 := by
  apply lucas_primality 102406289 (3 : ZMod 102406289)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) = 102406289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_683
      · exact prime_oneHundredCT_9371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102406289) ^ 51203144 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 149936 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 10928 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_104797937 : Nat.Prime 104797937 := by
  apply lucas_primality 104797937 (3 : ZMod 104797937)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (284777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (284777, 1)] : List FactorBlock).map factorBlockValue).prod) = 104797937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_284777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104797937) ^ 52398968 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 104797937) ^ 4556432 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 104797937) ^ 368 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_115829437 : Nat.Prime 115829437 := by
  apply lucas_primality 115829437 (5 : ZMod 115829437)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9652453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9652453, 1)] : List FactorBlock).map factorBlockValue).prod) = 115829437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_9652453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 115829437) ^ 57914718 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115829437) ^ 38609812 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 115829437) ^ 12 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_119616113 : Nat.Prime 119616113 := by
  apply lucas_primality 119616113 (3 : ZMod 119616113)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (79, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (79, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 119616113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_79
      · exact prime_oneHundredCT_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119616113) ^ 59808056 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 119616113) ^ 17088016 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 119616113) ^ 10874192 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 119616113) ^ 1514128 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 119616113) ^ 97328 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_124697981 : Nat.Prime 124697981 := by
  apply lucas_primality 124697981 (3 : ZMod 124697981)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (103, 1), (5503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (103, 1), (5503, 1)] : List FactorBlock).map factorBlockValue).prod) = 124697981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_103
      · exact prime_oneHundredCT_5503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 124697981) ^ 62348990 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 124697981) ^ 24939596 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 124697981) ^ 11336180 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 124697981) ^ 1210660 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 124697981) ^ 22660 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_133895743 : Nat.Prime 133895743 := by
  apply lucas_primality 133895743 (6 : ZMod 133895743)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (970259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (970259, 1)] : List FactorBlock).map factorBlockValue).prod) = 133895743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_970259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 133895743) ^ 66947871 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 133895743) ^ 44631914 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 133895743) ^ 5821554 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 133895743) ^ 138 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_144909313 : Nat.Prime 144909313 := by
  apply lucas_primality 144909313 (11 : ZMod 144909313)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (43, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (43, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 144909313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 144909313) ^ 72454656 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 144909313) ^ 48303104 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 144909313) ^ 3369984 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 144909313) ^ 132096 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_148948819 : Nat.Prime 148948819 := by
  apply lucas_primality 148948819 (2 : ZMod 148948819)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (43, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (43, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) = 148948819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_41
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_14081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148948819) ^ 74474409 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 148948819) ^ 49649606 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 148948819) ^ 3632898 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 148948819) ^ 3463926 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 148948819) ^ 10578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_150071237 : Nat.Prime 150071237 := by
  apply lucas_primality 150071237 (3 : ZMod 150071237)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (541, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (541, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) = 150071237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_541
      · exact prime_oneHundredCT_9907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150071237) ^ 75035618 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 21438748 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 277396 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 15148 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_154727593 : Nat.Prime 154727593 := by
  apply lucas_primality 154727593 (5 : ZMod 154727593)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (281, 1), (22943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (281, 1), (22943, 1)] : List FactorBlock).map factorBlockValue).prod) = 154727593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_281
      · exact prime_oneHundredCT_22943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 154727593) ^ 77363796 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 51575864 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 550632 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 154727593) ^ 6744 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_159007399 : Nat.Prime 159007399 := by
  apply lucas_primality 159007399 (3 : ZMod 159007399)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2409203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2409203, 1)] : List FactorBlock).map factorBlockValue).prod) = 159007399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_2409203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 159007399) ^ 79503699 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 159007399) ^ 53002466 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 159007399) ^ 14455218 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 159007399) ^ 66 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_159935459 : Nat.Prime 159935459 := by
  apply lucas_primality 159935459 (2 : ZMod 159935459)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2657, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2657, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) = 159935459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2657
      · exact prime_oneHundredCT_30097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 159935459) ^ 79967729 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 159935459) ^ 60194 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 159935459) ^ 5314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_204812579 : Nat.Prime 204812579 := by
  apply lucas_primality 204812579 (2 : ZMod 204812579)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) = 204812579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_102406289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204812579) ^ 102406289 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 204812579) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_210430769 : Nat.Prime 210430769 := by
  apply lucas_primality 210430769 (3 : ZMod 210430769)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) = 210430769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13151923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 210430769) ^ 105215384 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 210430769) ^ 16 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_216251809 : Nat.Prime 216251809 := by
  apply lucas_primality 216251809 (13 : ZMod 216251809)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2252623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2252623, 1)] : List FactorBlock).map factorBlockValue).prod) = 216251809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2252623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 216251809) ^ 108125904 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 216251809) ^ 72083936 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 216251809) ^ 96 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_225625909 : Nat.Prime 225625909 := by
  apply lucas_primality 225625909 (2 : ZMod 225625909)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (173, 1), (251, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (173, 1), (251, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod) = 225625909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_173
      · exact prime_oneHundredCT_251
      · exact prime_oneHundredCT_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 225625909) ^ 112812954 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 225625909) ^ 75208636 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 225625909) ^ 1304196 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 225625909) ^ 898908 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 225625909) ^ 521076 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_228051497 : Nat.Prime 228051497 := by
  apply lucas_primality 228051497 (3 : ZMod 228051497)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (28506437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (28506437, 1)] : List FactorBlock).map factorBlockValue).prod) = 228051497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_28506437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 228051497) ^ 114025748 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 228051497) ^ 8 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_238458593 : Nat.Prime 238458593 := by
  apply lucas_primality 238458593 (3 : ZMod 238458593)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (97, 1), (4519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (97, 1), (4519, 1)] : List FactorBlock).map factorBlockValue).prod) = 238458593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_97
      · exact prime_oneHundredCT_4519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 238458593) ^ 119229296 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 238458593) ^ 14026976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 238458593) ^ 2458336 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 238458593) ^ 52768 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_258169969 : Nat.Prime 258169969 := by
  apply lucas_primality 258169969 (11 : ZMod 258169969)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (256121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (256121, 1)] : List FactorBlock).map factorBlockValue).prod) = 258169969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_256121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 258169969) ^ 129084984 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 258169969) ^ 86056656 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 258169969) ^ 36881424 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 258169969) ^ 1008 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_267097681 : Nat.Prime 267097681 := by
  apply lucas_primality 267097681 (13 : ZMod 267097681)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) = 267097681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_107
      · exact prime_oneHundredCT_3467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 267097681) ^ 133548840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 89032560 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 53419536 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 2496240 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 77040 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_269391113 : Nat.Prime 269391113 := by
  apply lucas_primality 269391113 (3 : ZMod 269391113)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1980817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1980817, 1)] : List FactorBlock).map factorBlockValue).prod) = 269391113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_1980817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 269391113) ^ 134695556 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 269391113) ^ 15846536 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 269391113) ^ 136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_270151933 : Nat.Prime 270151933 := by
  apply lucas_primality 270151933 (2 : ZMod 270151933)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (22512661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (22512661, 1)] : List FactorBlock).map factorBlockValue).prod) = 270151933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_22512661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 270151933) ^ 135075966 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 270151933) ^ 90050644 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 270151933) ^ 12 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_282972779 : Nat.Prime 282972779 := by
  apply lucas_primality 282972779 (2 : ZMod 282972779)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (29, 1), (61, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (29, 1), (61, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 282972779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_61
      · exact prime_oneHundredCT_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 282972779) ^ 141486389 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282972779) ^ 25724798 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282972779) ^ 9757682 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282972779) ^ 4638898 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 282972779) ^ 428098 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_12539
      · exact prime_oneHundredCT_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_372274039 : Nat.Prime 372274039 := by
  apply lucas_primality 372274039 (3 : ZMod 372274039)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (20681891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (20681891, 1)] : List FactorBlock).map factorBlockValue).prod) = 372274039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_20681891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 372274039) ^ 186137019 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 372274039) ^ 124091346 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 372274039) ^ 18 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_385491529 : Nat.Prime 385491529 := by
  apply lucas_primality 385491529 (13 : ZMod 385491529)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (1784683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (1784683, 1)] : List FactorBlock).map factorBlockValue).prod) = 385491529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1784683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 385491529) ^ 192745764 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 385491529) ^ 128497176 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 385491529) ^ 216 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_390211117 : Nat.Prime 390211117 := by
  apply lucas_primality 390211117 (2 : ZMod 390211117)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2549, 1), (12757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2549, 1), (12757, 1)] : List FactorBlock).map factorBlockValue).prod) = 390211117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2549
      · exact prime_oneHundredCT_12757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 390211117) ^ 195105558 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 390211117) ^ 130070372 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 390211117) ^ 153084 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 390211117) ^ 30588 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_426966413 : Nat.Prime 426966413 := by
  apply lucas_primality 426966413 (2 : ZMod 426966413)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) = 426966413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_421
      · exact prime_oneHundredCT_253543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 426966413) ^ 213483206 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1014172 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1684 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_446511433 : Nat.Prime 446511433 := by
  apply lucas_primality 446511433 (10 : ZMod 446511433)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) = 446511433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_53
      · exact prime_oneHundredCT_351031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 446511433) ^ 223255716 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 148837144 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 8424744 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 1272 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_452200691 : Nat.Prime 452200691 := by
  apply lucas_primality 452200691 (2 : ZMod 452200691)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (509, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (509, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 452200691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_509
      · exact prime_oneHundredCT_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 452200691) ^ 226100345 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452200691) ^ 90440138 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452200691) ^ 6194530 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452200691) ^ 888410 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 452200691) ^ 371570 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_476917187 : Nat.Prime 476917187 := by
  apply lucas_primality 476917187 (2 : ZMod 476917187)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (238458593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (238458593, 1)] : List FactorBlock).map factorBlockValue).prod) = 476917187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_238458593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 476917187) ^ 238458593 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 476917187) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_484478327 : Nat.Prime 484478327 := by
  apply lucas_primality 484478327 (5 : ZMod 484478327)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2141, 1), (113143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2141, 1), (113143, 1)] : List FactorBlock).map factorBlockValue).prod) = 484478327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2141
      · exact prime_oneHundredCT_113143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 484478327) ^ 242239163 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 484478327) ^ 226286 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 484478327) ^ 4282 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_492432713 : Nat.Prime 492432713 := by
  apply lucas_primality 492432713 (3 : ZMod 492432713)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (811, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (811, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 492432713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_811
      · exact prime_oneHundredCT_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 492432713) ^ 246216356 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 6935672 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 607192 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 492432713) ^ 460648 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_503939587 : Nat.Prime 503939587 := by
  apply lucas_primality 503939587 (2 : ZMod 503939587)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (1150547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (1150547, 1)] : List FactorBlock).map factorBlockValue).prod) = 503939587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_1150547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 503939587) ^ 251969793 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 503939587) ^ 167979862 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 503939587) ^ 6903282 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 503939587) ^ 438 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_535582973 : Nat.Prime 535582973 := by
  apply lucas_primality 535582973 (2 : ZMod 535582973)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (133895743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (133895743, 1)] : List FactorBlock).map factorBlockValue).prod) = 535582973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_133895743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 535582973) ^ 267791486 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 535582973) ^ 4 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_565945559 : Nat.Prime 565945559 := by
  apply lucas_primality 565945559 (7 : ZMod 565945559)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (282972779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (282972779, 1)] : List FactorBlock).map factorBlockValue).prod) = 565945559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_282972779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 565945559) ^ 282972779 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 565945559) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_642820147 : Nat.Prime 642820147 := by
  apply lucas_primality 642820147 (2 : ZMod 642820147)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (53, 1), (179, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (53, 1), (179, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 642820147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_53
      · exact prime_oneHundredCT_179
      · exact prime_oneHundredCT_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642820147) ^ 321410073 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 214273382 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 27948702 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 12128682 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 3591174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 642820147) ^ 1309206 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_679311571 : Nat.Prime 679311571 := by
  apply lucas_primality 679311571 (2 : ZMod 679311571)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) = 679311571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_127
      · exact prime_oneHundredCT_25471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 679311571) ^ 339655785 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 226437190 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 135862314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 97044510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 5348910 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 26670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_695172277 : Nat.Prime 695172277 := by
  apply lucas_primality 695172277 (5 : ZMod 695172277)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (179, 1), (233, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (179, 1), (233, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 695172277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_179
      · exact prime_oneHundredCT_233
      · exact prime_oneHundredCT_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 695172277) ^ 347586138 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 695172277) ^ 231724092 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 695172277) ^ 3883644 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 695172277) ^ 2983572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 695172277) ^ 1501452 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17203
      · exact prime_oneHundredCT_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_762682541 : Nat.Prime 762682541 := by
  apply lucas_primality 762682541 (3 : ZMod 762682541)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (38134127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (38134127, 1)] : List FactorBlock).map factorBlockValue).prod) = 762682541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_38134127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 762682541) ^ 381341270 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 762682541) ^ 152536508 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 762682541) ^ 20 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_865007237 : Nat.Prime 865007237 := by
  apply lucas_primality 865007237 (2 : ZMod 865007237)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (216251809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (216251809, 1)] : List FactorBlock).map factorBlockValue).prod) = 865007237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_216251809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 865007237) ^ 432503618 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 865007237) ^ 4 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1086077747 : Nat.Prime 1086077747 := by
  apply lucas_primality 1086077747 (5 : ZMod 1086077747)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (43, 1), (31337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (43, 1), (31337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1086077747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_31337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1086077747) ^ 543038873 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1086077747) ^ 83544442 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1086077747) ^ 35034766 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1086077747) ^ 25257622 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1086077747) ^ 34658 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1279484057 : Nat.Prime 1279484057 := by
  apply lucas_primality 1279484057 (3 : ZMod 1279484057)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (9407971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (9407971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1279484057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_9407971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1279484057) ^ 639742028 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279484057) ^ 75263768 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1279484057) ^ 136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1429969789 : Nat.Prime 1429969789 := by
  apply lucas_primality 1429969789 (2 : ZMod 1429969789)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (13, 1), (211, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (13, 1), (211, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1429969789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_211
      · exact prime_oneHundredCT_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1429969789) ^ 714984894 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1429969789) ^ 476656596 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1429969789) ^ 109997676 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1429969789) ^ 6777108 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1429969789) ^ 888732 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1611172153 : Nat.Prime 1611172153 := by
  apply lucas_primality 1611172153 (5 : ZMod 1611172153)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (22377391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (22377391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611172153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_22377391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1611172153) ^ 805586076 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1611172153) ^ 537057384 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1611172153) ^ 72 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2088832103 : Nat.Prime 2088832103 := by
  apply lucas_primality 2088832103 (5 : ZMod 2088832103)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (862441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (862441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2088832103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_173
      · exact prime_oneHundredCT_862441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2088832103) ^ 1044416051 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2088832103) ^ 298404586 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2088832103) ^ 12074174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2088832103) ^ 2422 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2187018947 : Nat.Prime 2187018947 := by
  apply lucas_primality 2187018947 (6 : ZMod 2187018947)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (109, 1), (30493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (109, 1), (30493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2187018947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_109
      · exact prime_oneHundredCT_30493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2187018947) ^ 1093509473 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2187018947) ^ 312431278 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2187018947) ^ 46532318 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2187018947) ^ 20064394 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2187018947) ^ 71722 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2213346269 : Nat.Prime 2213346269 := by
  apply lucas_primality 2213346269 (2 : ZMod 2213346269)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213346269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11292583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2213346269) ^ 1106673134 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 316192324 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 196 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2695349743 : Nat.Prime 2695349743 := by
  apply lucas_primality 2695349743 (3 : ZMod 2695349743)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (1251323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (1251323, 1)] : List FactorBlock).map factorBlockValue).prod) = 2695349743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_359
      · exact prime_oneHundredCT_1251323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2695349743) ^ 1347674871 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695349743) ^ 898449914 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695349743) ^ 7507938 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2695349743) ^ 2154 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3086728291 : Nat.Prime 3086728291 := by
  apply lucas_primality 3086728291 (3 : ZMod 3086728291)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (47, 1), (79, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (47, 1), (79, 1), (3079, 1)] : List FactorBlock).map factorBlockValue).prod) = 3086728291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_79
      · exact prime_oneHundredCT_3079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3086728291) ^ 1543364145 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3086728291) ^ 1028909430 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3086728291) ^ 617345658 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3086728291) ^ 65675070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3086728291) ^ 39072510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3086728291) ^ 1002510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3192720959 : Nat.Prime 3192720959 := by
  apply lucas_primality 3192720959 (7 : ZMod 3192720959)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (228051497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (228051497, 1)] : List FactorBlock).map factorBlockValue).prod) = 3192720959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_228051497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3192720959) ^ 1596360479 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3192720959) ^ 456102994 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3192720959) ^ 14 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3213497839 : Nat.Prime 3213497839 := by
  apply lucas_primality 3213497839 (3 : ZMod 3213497839)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (535582973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (535582973, 1)] : List FactorBlock).map factorBlockValue).prod) = 3213497839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_535582973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3213497839) ^ 1606748919 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3213497839) ^ 1071165946 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3213497839) ^ 6 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3414362117 : Nat.Prime 3414362117 := by
  apply lucas_primality 3414362117 (2 : ZMod 3414362117)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (77599139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (77599139, 1)] : List FactorBlock).map factorBlockValue).prod) = 3414362117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_77599139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3414362117) ^ 1707181058 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414362117) ^ 310396556 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414362117) ^ 44 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3566049547 : Nat.Prime 3566049547 := by
  apply lucas_primality 3566049547 (2 : ZMod 3566049547)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3566049547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1481
      · exact prime_oneHundredCT_401311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3566049547) ^ 1783024773 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 1188683182 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 2407866 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 8886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3643890707 : Nat.Prime 3643890707 := by
  apply lucas_primality 3643890707 (2 : ZMod 3643890707)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (3710683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (3710683, 1)] : List FactorBlock).map factorBlockValue).prod) = 3643890707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_491
      · exact prime_oneHundredCT_3710683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3643890707) ^ 1821945353 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3643890707) ^ 7421366 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3643890707) ^ 982 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3782782589 : Nat.Prime 3782782589 := by
  apply lucas_primality 3782782589 (3 : ZMod 3782782589)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (71, 1), (1024589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (71, 1), (1024589, 1)] : List FactorBlock).map factorBlockValue).prod) = 3782782589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_1024589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3782782589) ^ 1891391294 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 290983276 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 53278628 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3782782589) ^ 3692 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_4177664207 : Nat.Prime 4177664207 := by
  apply lucas_primality 4177664207 (5 : ZMod 4177664207)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2088832103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2088832103, 1)] : List FactorBlock).map factorBlockValue).prod) = 4177664207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2088832103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4177664207) ^ 2088832103 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4177664207) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_4463126029 : Nat.Prime 4463126029 := by
  apply lucas_primality 4463126029 (2 : ZMod 4463126029)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (41325241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (41325241, 1)] : List FactorBlock).map factorBlockValue).prod) = 4463126029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_41325241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4463126029) ^ 2231563014 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4463126029) ^ 1487708676 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4463126029) ^ 108 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_5121144997 : Nat.Prime 5121144997 := by
  apply lucas_primality 5121144997 (2 : ZMod 5121144997)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1453, 1), (26701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1453, 1), (26701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5121144997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_1453
      · exact prime_oneHundredCT_26701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5121144997) ^ 2560572498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5121144997) ^ 1707048332 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5121144997) ^ 465558636 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5121144997) ^ 3524532 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5121144997) ^ 191796 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_5781168313 : Nat.Prime 5781168313 := by
  apply lucas_primality 5781168313 (5 : ZMod 5781168313)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (1061, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (1061, 1), (9871, 1)] : List FactorBlock).map factorBlockValue).prod) = 5781168313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_1061
      · exact prime_oneHundredCT_9871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5781168313) ^ 2890584156 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5781168313) ^ 1927056104 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5781168313) ^ 251355144 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5781168313) ^ 5448792 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 5781168313) ^ 585672 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6105189901 : Nat.Prime 6105189901 := by
  apply lucas_primality 6105189901 (10 : ZMod 6105189901)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (359, 1), (56687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (359, 1), (56687, 1)] : List FactorBlock).map factorBlockValue).prod) = 6105189901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_359
      · exact prime_oneHundredCT_56687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6105189901) ^ 3052594950 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 6105189901) ^ 2035063300 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 6105189901) ^ 1221037980 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 6105189901) ^ 17006100 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 6105189901) ^ 107700 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6385441919 : Nat.Prime 6385441919 := by
  apply lucas_primality 6385441919 (19 : ZMod 6385441919)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3192720959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3192720959, 1)] : List FactorBlock).map factorBlockValue).prod) = 6385441919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3192720959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (19 : ZMod 6385441919) ^ 3192720959 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (19 : ZMod 6385441919) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6938847523 : Nat.Prime 6938847523 := by
  apply lucas_primality 6938847523 (2 : ZMod 6938847523)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (385491529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (385491529, 1)] : List FactorBlock).map factorBlockValue).prod) = 6938847523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_385491529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6938847523) ^ 3469423761 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6938847523) ^ 2312949174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6938847523) ^ 18 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_7369330403 : Nat.Prime 7369330403 := by
  apply lucas_primality 7369330403 (2 : ZMod 7369330403)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (67, 1), (709, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (67, 1), (709, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 7369330403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_67
      · exact prime_oneHundredCT_709
      · exact prime_oneHundredCT_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7369330403) ^ 3684665201 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 1052761486 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 109990006 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 10393978 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7369330403) ^ 4655294 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_11061581833 : Nat.Prime 11061581833 := by
  apply lucas_primality 11061581833 (5 : ZMod 11061581833)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (1045123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (1045123, 1)] : List FactorBlock).map factorBlockValue).prod) = 11061581833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_1045123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11061581833) ^ 5530790916 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 3687193944 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 1580225976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11061581833) ^ 10584 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_11075391241 : Nat.Prime 11075391241 := by
  apply lucas_primality 11075391241 (14 : ZMod 11075391241)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (659, 1), (140053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (659, 1), (140053, 1)] : List FactorBlock).map factorBlockValue).prod) = 11075391241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_659
      · exact prime_oneHundredCT_140053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 11075391241) ^ 5537695620 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 3691797080 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 2215078248 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 16806360 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 11075391241) ^ 79080 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_12748193219 : Nat.Prime 12748193219 := by
  apply lucas_primality 12748193219 (2 : ZMod 12748193219)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1697, 1), (3756097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1697, 1), (3756097, 1)] : List FactorBlock).map factorBlockValue).prod) = 12748193219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_1697
      · exact prime_oneHundredCT_3756097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12748193219) ^ 6374096609 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12748193219) ^ 7512194 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12748193219) ^ 3394 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_15461000459 : Nat.Prime 15461000459 := by
  apply lucas_primality 15461000459 (2 : ZMod 15461000459)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27539, 1), (280711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27539, 1), (280711, 1)] : List FactorBlock).map factorBlockValue).prod) = 15461000459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_27539
      · exact prime_oneHundredCT_280711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15461000459) ^ 7730500229 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15461000459) ^ 561422 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15461000459) ^ 55078 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_16612519487 : Nat.Prime 16612519487 := by
  apply lucas_primality 16612519487 (5 : ZMod 16612519487)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (9157949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (9157949, 1)] : List FactorBlock).map factorBlockValue).prod) = 16612519487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_907
      · exact prime_oneHundredCT_9157949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16612519487) ^ 8306259743 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16612519487) ^ 18315898 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16612519487) ^ 1814 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_16937230103 : Nat.Prime 16937230103 := by
  apply lucas_primality 16937230103 (5 : ZMod 16937230103)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1667, 1), (390781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1667, 1), (390781, 1)] : List FactorBlock).map factorBlockValue).prod) = 16937230103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_1667
      · exact prime_oneHundredCT_390781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16937230103) ^ 8468615051 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 1302863854 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 10160306 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16937230103) ^ 43342 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_19358100161 : Nat.Prime 19358100161 := by
  apply lucas_primality 19358100161 (3 : ZMod 19358100161)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (103, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (103, 1), (83903, 1)] : List FactorBlock).map factorBlockValue).prod) = 19358100161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_103
      · exact prime_oneHundredCT_83903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19358100161) ^ 9679050080 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 3871620032 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 2765442880 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 187942720 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 19358100161) ^ 230720 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_19464823757 : Nat.Prime 19464823757 := by
  apply lucas_primality 19464823757 (2 : ZMod 19464823757)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (695172277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (695172277, 1)] : List FactorBlock).map factorBlockValue).prod) = 19464823757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_695172277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19464823757) ^ 9732411878 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19464823757) ^ 2780689108 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19464823757) ^ 28 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_22853080729 : Nat.Prime 22853080729 := by
  apply lucas_primality 22853080729 (11 : ZMod 22853080729)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2909, 1), (109111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2909, 1), (109111, 1)] : List FactorBlock).map factorBlockValue).prod) = 22853080729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2909
      · exact prime_oneHundredCT_109111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 22853080729) ^ 11426540364 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 22853080729) ^ 7617693576 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 22853080729) ^ 7855992 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 22853080729) ^ 209448 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_79
      · exact prime_oneHundredCT_163
      · exact prime_oneHundredCT_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_24121994333 : Nat.Prime 24121994333 := by
  apply lucas_primality 24121994333 (2 : ZMod 24121994333)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (157, 1), (1324511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (157, 1), (1324511, 1)] : List FactorBlock).map factorBlockValue).prod) = 24121994333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_157
      · exact prime_oneHundredCT_1324511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24121994333) ^ 12060997166 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24121994333) ^ 831792908 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24121994333) ^ 153643276 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24121994333) ^ 18212 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_4621
      · exact prime_oneHundredCT_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_26896283387 : Nat.Prime 26896283387 := by
  apply lucas_primality 26896283387 (2 : ZMod 26896283387)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26896283387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_51923327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26896283387) ^ 13448141693 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 3842326198 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 726926578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 518 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_27075109081 : Nat.Prime 27075109081 := by
  apply lucas_primality 27075109081 (14 : ZMod 27075109081)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (225625909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (225625909, 1)] : List FactorBlock).map factorBlockValue).prod) = 27075109081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_225625909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 27075109081) ^ 13537554540 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 27075109081) ^ 9025036360 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 27075109081) ^ 5415021816 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 27075109081) ^ 120 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_30726869983 : Nat.Prime 30726869983 := by
  apply lucas_primality 30726869983 (5 : ZMod 30726869983)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5121144997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5121144997, 1)] : List FactorBlock).map factorBlockValue).prod) = 30726869983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5121144997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30726869983) ^ 15363434991 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 30726869983) ^ 10242289994 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 30726869983) ^ 6 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_30867282911 : Nat.Prime 30867282911 := by
  apply lucas_primality 30867282911 (11 : ZMod 30867282911)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3086728291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3086728291, 1)] : List FactorBlock).map factorBlockValue).prod) = 30867282911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_3086728291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 30867282911) ^ 15433641455 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 30867282911) ^ 6173456582 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 30867282911) ^ 10 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_38716200323 : Nat.Prime 38716200323 := by
  apply lucas_primality 38716200323 (2 : ZMod 38716200323)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19358100161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19358100161, 1)] : List FactorBlock).map factorBlockValue).prod) = 38716200323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19358100161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 38716200323) ^ 19358100161 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 38716200323) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_43064212757 : Nat.Prime 43064212757 := by
  apply lucas_primality 43064212757 (2 : ZMod 43064212757)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (81233, 1), (132533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (81233, 1), (132533, 1)] : List FactorBlock).map factorBlockValue).prod) = 43064212757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_81233
      · exact prime_oneHundredCT_132533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43064212757) ^ 21532106378 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43064212757) ^ 530132 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 43064212757) ^ 324932 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_44997410291 : Nat.Prime 44997410291 := by
  apply lucas_primality 44997410291 (2 : ZMod 44997410291)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (642820147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (642820147, 1)] : List FactorBlock).map factorBlockValue).prod) = 44997410291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_642820147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44997410291) ^ 22498705145 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 8999482058 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 6428201470 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 44997410291) ^ 70 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_47423310787 : Nat.Prime 47423310787 := by
  apply lucas_primality 47423310787 (2 : ZMod 47423310787)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) = 47423310787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_131
      · exact prime_oneHundredCT_6703889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47423310787) ^ 23711655393 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 15807770262 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 362010006 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 7074 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_47978500289 : Nat.Prime 47978500289 := by
  apply lucas_primality 47978500289 (6 : ZMod 47978500289)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37, 1), (20261191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37, 1), (20261191, 1)] : List FactorBlock).map factorBlockValue).prod) = 47978500289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_20261191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 47978500289) ^ 23989250144 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 47978500289) ^ 1296716224 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 47978500289) ^ 2368 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_49116821639 : Nat.Prime 49116821639 := by
  apply lucas_primality 49116821639 (7 : ZMod 49116821639)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (103, 1), (5544911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (103, 1), (5544911, 1)] : List FactorBlock).map factorBlockValue).prod) = 49116821639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_103
      · exact prime_oneHundredCT_5544911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49116821639) ^ 24558410819 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 49116821639) ^ 1142251666 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 49116821639) ^ 476862346 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 49116821639) ^ 8858 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_52199887279 : Nat.Prime 52199887279 := by
  apply lucas_primality 52199887279 (3 : ZMod 52199887279)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (179, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (179, 1), (90173, 1)] : List FactorBlock).map factorBlockValue).prod) = 52199887279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_179
      · exact prime_oneHundredCT_90173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52199887279) ^ 26099943639 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52199887279) ^ 17399962426 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52199887279) ^ 7457126754 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52199887279) ^ 4745444298 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52199887279) ^ 291619482 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 52199887279) ^ 578886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_52430123219 : Nat.Prime 52430123219 := by
  apply lucas_primality 52430123219 (2 : ZMod 52430123219)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (73, 2), (447211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (73, 2), (447211, 1)] : List FactorBlock).map factorBlockValue).prod) = 52430123219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_447211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52430123219) ^ 26215061609 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 52430123219) ^ 4766374838 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 52430123219) ^ 718220866 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 52430123219) ^ 117238 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_66274533293 : Nat.Prime 66274533293 := by
  apply lucas_primality 66274533293 (2 : ZMod 66274533293)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1291, 1), (1166723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1291, 1), (1166723, 1)] : List FactorBlock).map factorBlockValue).prod) = 66274533293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_1291
      · exact prime_oneHundredCT_1166723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66274533293) ^ 33137266646 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 6024957572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 51335812 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 56804 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_68758894037 : Nat.Prime 68758894037 := by
  apply lucas_primality 68758894037 (3 : ZMod 68758894037)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (41, 1), (379, 1), (6871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (41, 1), (379, 1), (6871, 1)] : List FactorBlock).map factorBlockValue).prod) = 68758894037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_41
      · exact prime_oneHundredCT_379
      · exact prime_oneHundredCT_6871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68758894037) ^ 34379447018 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68758894037) ^ 9822699148 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68758894037) ^ 2989517132 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68758894037) ^ 1677046196 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68758894037) ^ 181421884 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68758894037) ^ 10007116 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_69137562031 : Nat.Prime 69137562031 := by
  apply lucas_primality 69137562031 (13 : ZMod 69137562031)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (193, 1), (11940857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (193, 1), (11940857, 1)] : List FactorBlock).map factorBlockValue).prod) = 69137562031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_193
      · exact prime_oneHundredCT_11940857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 69137562031) ^ 34568781015 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 69137562031) ^ 23045854010 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 69137562031) ^ 13827512406 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 69137562031) ^ 358225710 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 69137562031) ^ 5790 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_87683238689 : Nat.Prime 87683238689 := by
  apply lucas_primality 87683238689 (3 : ZMod 87683238689)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) = 87683238689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_149
      · exact prime_oneHundredCT_251917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87683238689) ^ 43841619344 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 1201140256 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 588478112 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 348064 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_107373267763 : Nat.Prime 107373267763 := by
  apply lucas_primality 107373267763 (2 : ZMod 107373267763)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) = 107373267763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_67
      · exact prime_oneHundredCT_267097681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107373267763) ^ 53686633881 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 35791089254 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 1602586086 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 402 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_853
      · exact prime_oneHundredCT_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_175198156807 : Nat.Prime 175198156807 := by
  apply lucas_primality 175198156807 (5 : ZMod 175198156807)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21221, 1), (1375981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21221, 1), (1375981, 1)] : List FactorBlock).map factorBlockValue).prod) = 175198156807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_21221
      · exact prime_oneHundredCT_1375981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 175198156807) ^ 87599078403 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 58399385602 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 8255886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 175198156807) ^ 127326 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_178584772031 : Nat.Prime 178584772031 := by
  apply lucas_primality 178584772031 (7 : ZMod 178584772031)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (150071237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (150071237, 1)] : List FactorBlock).map factorBlockValue).prod) = 178584772031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_150071237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178584772031) ^ 89292386015 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 35716954406 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 25512110290 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 10504986590 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 1190 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_183155697031 : Nat.Prime 183155697031 := by
  apply lucas_primality 183155697031 (23 : ZMod 183155697031)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6105189901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6105189901, 1)] : List FactorBlock).map factorBlockValue).prod) = 183155697031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_6105189901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 183155697031) ^ 91577848515 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 183155697031) ^ 61051899010 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 183155697031) ^ 36631139406 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 183155697031) ^ 30 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_197335830883 : Nat.Prime 197335830883 := by
  apply lucas_primality 197335830883 (2 : ZMod 197335830883)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1429969789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1429969789, 1)] : List FactorBlock).map factorBlockValue).prod) = 197335830883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_1429969789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197335830883) ^ 98667915441 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 197335830883) ^ 65778610294 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 197335830883) ^ 8579818734 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 197335830883) ^ 138 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_208799549117 : Nat.Prime 208799549117 := by
  apply lucas_primality 208799549117 (2 : ZMod 208799549117)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52199887279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52199887279, 1)] : List FactorBlock).map factorBlockValue).prod) = 208799549117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_52199887279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 208799549117) ^ 104399774558 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 208799549117) ^ 4 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_212734755587 : Nat.Prime 212734755587 := by
  apply lucas_primality 212734755587 (2 : ZMod 212734755587)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (853, 1), (124697981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (853, 1), (124697981, 1)] : List FactorBlock).map factorBlockValue).prod) = 212734755587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_853
      · exact prime_oneHundredCT_124697981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 212734755587) ^ 106367377793 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 212734755587) ^ 249395962 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 212734755587) ^ 1706 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_216454006427 : Nat.Prime 216454006427 := by
  apply lucas_primality 216454006427 (2 : ZMod 216454006427)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (15461000459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (15461000459, 1)] : List FactorBlock).map factorBlockValue).prod) = 216454006427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_15461000459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216454006427) ^ 108227003213 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 216454006427) ^ 30922000918 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 216454006427) ^ 14 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_259397143063 : Nat.Prime 259397143063 := by
  apply lucas_primality 259397143063 (3 : ZMod 259397143063)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1151, 1), (37561127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1151, 1), (37561127, 1)] : List FactorBlock).map factorBlockValue).prod) = 259397143063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1151
      · exact prime_oneHundredCT_37561127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 259397143063) ^ 129698571531 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 86465714354 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 225366762 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 259397143063) ^ 6906 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_276887636227 : Nat.Prime 276887636227 := by
  apply lucas_primality 276887636227 (2 : ZMod 276887636227)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (107, 1), (181, 1), (264757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (107, 1), (181, 1), (264757, 1)] : List FactorBlock).map factorBlockValue).prod) = 276887636227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_107
      · exact prime_oneHundredCT_181
      · exact prime_oneHundredCT_264757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 276887636227) ^ 138443818113 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 92295878742 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 2587734918 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 1529765946 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 276887636227) ^ 1045818 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_285191559557 : Nat.Prime 285191559557 := by
  apply lucas_primality 285191559557 (2 : ZMod 285191559557)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (26591, 1), (72467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (26591, 1), (72467, 1)] : List FactorBlock).map factorBlockValue).prod) = 285191559557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_26591
      · exact prime_oneHundredCT_72467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 285191559557) ^ 142595779778 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 285191559557) ^ 7707879988 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 285191559557) ^ 10725116 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 285191559557) ^ 3935468 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_301513955551 : Nat.Prime 301513955551 := by
  apply lucas_primality 301513955551 (3 : ZMod 301513955551)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (69313553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (69313553, 1)] : List FactorBlock).map factorBlockValue).prod) = 301513955551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_69313553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 301513955551) ^ 150756977775 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 301513955551) ^ 100504651850 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 301513955551) ^ 60302791110 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 301513955551) ^ 10397032950 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 301513955551) ^ 4350 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_357169544063 : Nat.Prime 357169544063 := by
  apply lucas_primality 357169544063 (5 : ZMod 357169544063)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (178584772031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (178584772031, 1)] : List FactorBlock).map factorBlockValue).prod) = 357169544063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_178584772031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 357169544063) ^ 178584772031 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 357169544063) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_392934573113 : Nat.Prime 392934573113 := by
  apply lucas_primality 392934573113 (3 : ZMod 392934573113)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (49116821639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (49116821639, 1)] : List FactorBlock).map factorBlockValue).prod) = 392934573113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_49116821639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 392934573113) ^ 196467286556 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 392934573113) ^ 8 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_407185568351 : Nat.Prime 407185568351 := by
  apply lucas_primality 407185568351 (7 : ZMod 407185568351)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (26893, 1), (27529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (26893, 1), (27529, 1)] : List FactorBlock).map factorBlockValue).prod) = 407185568351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_26893
      · exact prime_oneHundredCT_27529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 407185568351) ^ 203592784175 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 407185568351) ^ 81437113670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 407185568351) ^ 37016869850 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 407185568351) ^ 15140950 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 407185568351) ^ 14791150 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_446011079209 : Nat.Prime 446011079209 := by
  apply lucas_primality 446011079209 (7 : ZMod 446011079209)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) = 446011079209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_829
      · exact prime_oneHundredCT_723133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 446011079209) ^ 223005539604 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 148670359736 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 14387454168 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 538010952 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 616776 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_499974182987 : Nat.Prime 499974182987 := by
  apply lucas_primality 499974182987 (5 : ZMod 499974182987)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (865007237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (865007237, 1)] : List FactorBlock).map factorBlockValue).prod) = 499974182987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_865007237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 499974182987) ^ 249987091493 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 499974182987) ^ 29410246058 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 499974182987) ^ 578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_549417252737 : Nat.Prime 549417252737 := by
  apply lucas_primality 549417252737 (3 : ZMod 549417252737)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11, 1), (390211117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11, 1), (390211117, 1)] : List FactorBlock).map factorBlockValue).prod) = 549417252737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_390211117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 549417252737) ^ 274708626368 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 549417252737) ^ 49947022976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 549417252737) ^ 1408 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_615051349459 : Nat.Prime 615051349459 := by
  apply lucas_primality 615051349459 (7 : ZMod 615051349459)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (419, 1), (2688467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (419, 1), (2688467, 1)] : List FactorBlock).map factorBlockValue).prod) = 615051349459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_419
      · exact prime_oneHundredCT_2688467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 615051349459) ^ 307525674729 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 205017116486 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 87864478494 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 47311642266 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 1467902982 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 615051349459) ^ 228774 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_659795388823 : Nat.Prime 659795388823 := by
  apply lucas_primality 659795388823 (6 : ZMod 659795388823)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) = 659795388823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_83
      · exact prime_oneHundredCT_103
      · exact prime_oneHundredCT_115883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 659795388823) ^ 329897694411 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 219931796274 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 17832307806 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 7949342034 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 6405780474 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 5693634 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_671678220533 : Nat.Prime 671678220533 := by
  apply lucas_primality 671678220533 (2 : ZMod 671678220533)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (492432713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (492432713, 1)] : List FactorBlock).map factorBlockValue).prod) = 671678220533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_492432713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 671678220533) ^ 335839110266 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 61061656412 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 21667039372 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 671678220533) ^ 1364 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_738747629527 : Nat.Prime 738747629527 := by
  apply lucas_primality 738747629527 (5 : ZMod 738747629527)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) = 738747629527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_52457
      · exact prime_oneHundredCT_2347153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 738747629527) ^ 369373814763 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 246249209842 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 14082918 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 314742 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_971937009349 : Nat.Prime 971937009349 := by
  apply lucas_primality 971937009349 (2 : ZMod 971937009349)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1619, 1), (50027641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1619, 1), (50027641, 1)] : List FactorBlock).map factorBlockValue).prod) = 971937009349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1619
      · exact prime_oneHundredCT_50027641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 971937009349) ^ 485968504674 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 323979003116 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 600331692 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 19428 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1022058768707 : Nat.Prime 1022058768707 := by
  apply lucas_primality 1022058768707 (2 : ZMod 1022058768707)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022058768707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_26896283387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1022058768707) ^ 511029384353 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 53792566774 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 38 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1343356441067 : Nat.Prime 1343356441067 := by
  apply lucas_primality 1343356441067 (2 : ZMod 1343356441067)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (671678220533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (671678220533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343356441067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_671678220533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1343356441067) ^ 671678220533 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343356441067) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1370014198489 : Nat.Prime 1370014198489 := by
  apply lucas_primality 1370014198489 (7 : ZMod 1370014198489)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370014198489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_13711
      · exact prime_oneHundredCT_106753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1370014198489) ^ 685007099244 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 456671399496 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 105385707576 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 99920808 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 12833496 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1498941933673 : Nat.Prime 1498941933673 := by
  apply lucas_primality 1498941933673 (5 : ZMod 1498941933673)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (431, 1), (144909313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (431, 1), (144909313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498941933673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_431
      · exact prime_oneHundredCT_144909313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1498941933673) ^ 749470966836 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1498941933673) ^ 499647311224 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1498941933673) ^ 3477823512 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1498941933673) ^ 10344 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1674813744997 : Nat.Prime 1674813744997 := by
  apply lucas_primality 1674813744997 (2 : ZMod 1674813744997)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (59, 1), (19878623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (59, 1), (19878623, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674813744997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_59
      · exact prime_oneHundredCT_19878623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1674813744997) ^ 837406872498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674813744997) ^ 558271248332 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674813744997) ^ 239259106428 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674813744997) ^ 98518455588 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674813744997) ^ 28386673644 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674813744997) ^ 84252 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1708095575761 : Nat.Prime 1708095575761 := by
  apply lucas_primality 1708095575761 (37 : ZMod 1708095575761)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (29, 1), (35059433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (29, 1), (35059433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1708095575761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_35059433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 1708095575761) ^ 854047787880 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (37 : ZMod 1708095575761) ^ 569365191920 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (37 : ZMod 1708095575761) ^ 341619115152 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (37 : ZMod 1708095575761) ^ 244013653680 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (37 : ZMod 1708095575761) ^ 58899847440 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (37 : ZMod 1708095575761) ^ 48720 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1720136143601 : Nat.Prime 1720136143601 := by
  apply lucas_primality 1720136143601 (3 : ZMod 1720136143601)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (89, 1), (6902633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (89, 1), (6902633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1720136143601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_89
      · exact prime_oneHundredCT_6902633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1720136143601) ^ 860068071800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1720136143601) ^ 344027228720 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1720136143601) ^ 245733734800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1720136143601) ^ 19327372400 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1720136143601) ^ 249200 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1731632051417 : Nat.Prime 1731632051417 := by
  apply lucas_primality 1731632051417 (3 : ZMod 1731632051417)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (216454006427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (216454006427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731632051417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_216454006427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1731632051417) ^ 865816025708 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1731632051417) ^ 8 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2262587459831 : Nat.Prime 2262587459831 := by
  apply lucas_primality 2262587459831 (43 : ZMod 2262587459831)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (127, 1), (104797937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (127, 1), (104797937, 1)] : List FactorBlock).map factorBlockValue).prod) = 2262587459831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_127
      · exact prime_oneHundredCT_104797937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 2262587459831) ^ 1131293729915 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (43 : ZMod 2262587459831) ^ 452517491966 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (43 : ZMod 2262587459831) ^ 133093379990 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (43 : ZMod 2262587459831) ^ 17815649290 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (43 : ZMod 2262587459831) ^ 21590 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2729490688553 : Nat.Prime 2729490688553 := by
  apply lucas_primality 2729490688553 (3 : ZMod 2729490688553)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729490688553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_173
      · exact prime_oneHundredCT_35069
      · exact prime_oneHundredCT_56237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2729490688553) ^ 1364745344276 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 15777402824 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 77832008 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 48535496 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2800878888487 : Nat.Prime 2800878888487 := by
  apply lucas_primality 2800878888487 (5 : ZMod 2800878888487)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (431, 1), (154727593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (431, 1), (154727593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2800878888487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_431
      · exact prime_oneHundredCT_154727593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2800878888487) ^ 1400439444243 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 933626296162 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 400125555498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 6498558906 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2800878888487) ^ 18102 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3330937342157 : Nat.Prime 3330937342157 := by
  apply lucas_primality 3330937342157 (2 : ZMod 3330937342157)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (7369330403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (7369330403, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330937342157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_113
      · exact prime_oneHundredCT_7369330403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3330937342157) ^ 1665468671078 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3330937342157) ^ 29477321612 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3330937342157) ^ 452 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3766125322919 : Nat.Prime 3766125322919 := by
  apply lucas_primality 3766125322919 (7 : ZMod 3766125322919)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (7019, 1), (485137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (7019, 1), (485137, 1)] : List FactorBlock).map factorBlockValue).prod) = 3766125322919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_79
      · exact prime_oneHundredCT_7019
      · exact prime_oneHundredCT_485137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3766125322919) ^ 1883062661459 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3766125322919) ^ 538017903274 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3766125322919) ^ 47672472442 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3766125322919) ^ 536561522 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 3766125322919) ^ 7763014 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_5721649413079 : Nat.Prime 5721649413079 := by
  apply lucas_primality 5721649413079 (6 : ZMod 5721649413079)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (67, 1), (36401429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (67, 1), (36401429, 1)] : List FactorBlock).map factorBlockValue).prod) = 5721649413079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_67
      · exact prime_oneHundredCT_36401429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5721649413079) ^ 2860824706539 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721649413079) ^ 1907216471026 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721649413079) ^ 336567612534 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721649413079) ^ 248767365786 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721649413079) ^ 85397752434 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721649413079) ^ 157182 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_7358318379431 : Nat.Prime 7358318379431 := by
  apply lucas_primality 7358318379431 (13 : ZMod 7358318379431)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (229, 1), (44016979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (229, 1), (44016979, 1)] : List FactorBlock).map factorBlockValue).prod) = 7358318379431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_229
      · exact prime_oneHundredCT_44016979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7358318379431) ^ 3679159189715 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 1471663675886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 100798881910 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 32132394670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (13 : ZMod 7358318379431) ^ 167170 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_7775787827411 : Nat.Prime 7775787827411 := by
  apply lucas_primality 7775787827411 (2 : ZMod 7775787827411)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1543, 1), (503939587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1543, 1), (503939587, 1)] : List FactorBlock).map factorBlockValue).prod) = 7775787827411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_1543
      · exact prime_oneHundredCT_503939587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7775787827411) ^ 3887893913705 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7775787827411) ^ 1555157565482 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7775787827411) ^ 5039395870 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7775787827411) ^ 15430 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_8450556055043 : Nat.Prime 8450556055043 := by
  apply lucas_primality 8450556055043 (2 : ZMod 8450556055043)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) = 8450556055043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_83
      · exact prime_oneHundredCT_2213346269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8450556055043) ^ 4225278027521 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 367415480654 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 101813928374 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 3818 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_9566065542823 : Nat.Prime 9566065542823 := by
  apply lucas_primality 9566065542823 (5 : ZMod 9566065542823)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566065542823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2347
      · exact prime_oneHundredCT_679311571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9566065542823) ^ 4783032771411 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 3188688514274 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 4075869426 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 14082 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_10223538369013 : Nat.Prime 10223538369013 := by
  apply lucas_primality 10223538369013 (2 : ZMod 10223538369013)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) = 10223538369013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_13147
      · exact prime_oneHundredCT_744859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10223538369013) ^ 5111769184506 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 3407846123004 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 352535805828 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 777632796 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 13725468 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_10228767061871 : Nat.Prime 10228767061871 := by
  apply lucas_primality 10228767061871 (7 : ZMod 10228767061871)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (23, 1), (281, 1), (1329971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (23, 1), (281, 1), (1329971, 1)] : List FactorBlock).map factorBlockValue).prod) = 10228767061871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_281
      · exact prime_oneHundredCT_1329971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10228767061871) ^ 5114383530935 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 2045753412374 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 1461252437410 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 601692180110 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 444729002690 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 36401306270 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 10228767061871) ^ 7690970 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_10556610755563 : Nat.Prime 10556610755563 := by
  apply lucas_primality 10556610755563 (2 : ZMod 10556610755563)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (30867282911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (30867282911, 1)] : List FactorBlock).map factorBlockValue).prod) = 10556610755563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_30867282911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10556610755563) ^ 5278305377781 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10556610755563) ^ 3518870251854 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10556610755563) ^ 555611092398 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10556610755563) ^ 342 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_10855680484993 : Nat.Prime 10855680484993 := by
  apply lucas_primality 10855680484993 (5 : ZMod 10855680484993)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (457, 1), (8837137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (457, 1), (8837137, 1)] : List FactorBlock).map factorBlockValue).prod) = 10855680484993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_457
      · exact prime_oneHundredCT_8837137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10855680484993) ^ 5427840242496 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855680484993) ^ 3618560161664 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855680484993) ^ 1550811497856 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855680484993) ^ 23754224256 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 10855680484993) ^ 1228416 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_14328271708661 : Nat.Prime 14328271708661 := by
  apply lucas_primality 14328271708661 (3 : ZMod 14328271708661)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (13, 1), (53, 1), (21220153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (13, 1), (53, 1), (21220153, 1)] : List FactorBlock).map factorBlockValue).prod) = 14328271708661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_53
      · exact prime_oneHundredCT_21220153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14328271708661) ^ 7164135854330 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14328271708661) ^ 2865654341732 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14328271708661) ^ 2046895958380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14328271708661) ^ 1102174746820 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14328271708661) ^ 270344749220 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14328271708661) ^ 675220 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_15331615327909 : Nat.Prime 15331615327909 := by
  apply lucas_primality 15331615327909 (2 : ZMod 15331615327909)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (38716200323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (38716200323, 1)] : List FactorBlock).map factorBlockValue).prod) = 15331615327909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_38716200323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15331615327909) ^ 7665807663954 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 5110538442636 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 1393783211628 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 15331615327909) ^ 396 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_21160885802867 : Nat.Prime 21160885802867 := by
  apply lucas_primality 21160885802867 (2 : ZMod 21160885802867)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (3782782589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (3782782589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21160885802867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2797
      · exact prime_oneHundredCT_3782782589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21160885802867) ^ 10580442901433 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 21160885802867) ^ 7565565178 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 21160885802867) ^ 5594 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_28962749561003 : Nat.Prime 28962749561003 := by
  apply lucas_primality 28962749561003 (2 : ZMod 28962749561003)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2087, 1), (6938847523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2087, 1), (6938847523, 1)] : List FactorBlock).map factorBlockValue).prod) = 28962749561003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2087
      · exact prime_oneHundredCT_6938847523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28962749561003) ^ 14481374780501 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28962749561003) ^ 13877695046 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28962749561003) ^ 4174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_36907600571927 : Nat.Prime 36907600571927 := by
  apply lucas_primality 36907600571927 (5 : ZMod 36907600571927)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (433, 1), (46475983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (433, 1), (46475983, 1)] : List FactorBlock).map factorBlockValue).prod) = 36907600571927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_131
      · exact prime_oneHundredCT_433
      · exact prime_oneHundredCT_46475983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36907600571927) ^ 18453800285963 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36907600571927) ^ 5272514367418 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36907600571927) ^ 281737408946 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36907600571927) ^ 85236952822 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 36907600571927) ^ 794122 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_40012680077077 : Nat.Prime 40012680077077 := by
  apply lucas_primality 40012680077077 (2 : ZMod 40012680077077)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) = 40012680077077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_335633
      · exact prime_oneHundredCT_1419233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40012680077077) ^ 20006340038538 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 13337560025692 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 5716097153868 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 119215572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 28193172 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_51712334066891 : Nat.Prime 51712334066891 := by
  apply lucas_primality 51712334066891 (2 : ZMod 51712334066891)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) = 51712334066891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_738747629527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51712334066891) ^ 25856167033445 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 10342466813378 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 7387476295270 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 70 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_96697
      · exact prime_oneHundredCT_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_62960806628351 : Nat.Prime 62960806628351 := by
  apply lucas_primality 62960806628351 (7 : ZMod 62960806628351)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (66274533293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (66274533293, 1)] : List FactorBlock).map factorBlockValue).prod) = 62960806628351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_66274533293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 62960806628351) ^ 31480403314175 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 12592161325670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 3313726664650 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 950 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_67877623794931 : Nat.Prime 67877623794931 := by
  apply lucas_primality 67877623794931 (3 : ZMod 67877623794931)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2262587459831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2262587459831, 1)] : List FactorBlock).map factorBlockValue).prod) = 67877623794931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_2262587459831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67877623794931) ^ 33938811897465 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67877623794931) ^ 22625874598310 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67877623794931) ^ 13575524758986 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 67877623794931) ^ 30 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_80942864418343 : Nat.Prime 80942864418343 := by
  apply lucas_primality 80942864418343 (5 : ZMod 80942864418343)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1498941933673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1498941933673, 1)] : List FactorBlock).map factorBlockValue).prod) = 80942864418343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1498941933673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 80942864418343) ^ 40471432209171 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 80942864418343) ^ 26980954806114 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 80942864418343) ^ 54 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_82512874416541 : Nat.Prime 82512874416541 := by
  apply lucas_primality 82512874416541 (17 : ZMod 82512874416541)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (31, 1), (683, 1), (2823971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (31, 1), (683, 1), (2823971, 1)] : List FactorBlock).map factorBlockValue).prod) = 82512874416541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_683
      · exact prime_oneHundredCT_2823971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 82512874416541) ^ 41256437208270 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 27504291472180 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 16502574883308 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 3587516278980 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 2661705626340 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 120809479380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 82512874416541) ^ 29218740 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_173
      · exact prime_oneHundredCT_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_117915411105367 : Nat.Prime 117915411105367 := by
  apply lucas_primality 117915411105367 (5 : ZMod 117915411105367)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (479, 1), (119616113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (479, 1), (119616113, 1)] : List FactorBlock).map factorBlockValue).prod) = 117915411105367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_479
      · exact prime_oneHundredCT_119616113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 117915411105367) ^ 58957705552683 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 117915411105367) ^ 39305137035122 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 117915411105367) ^ 16845058729338 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 117915411105367) ^ 246169960554 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 117915411105367) ^ 985782 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_122314386981697 : Nat.Prime 122314386981697 := by
  apply lucas_primality 122314386981697 (15 : ZMod 122314386981697)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (13, 1), (47, 1), (148948819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (13, 1), (47, 1), (148948819, 1)] : List FactorBlock).map factorBlockValue).prod) = 122314386981697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_148948819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 122314386981697) ^ 61157193490848 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (15 : ZMod 122314386981697) ^ 40771462327232 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (15 : ZMod 122314386981697) ^ 17473483854528 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (15 : ZMod 122314386981697) ^ 9408798998592 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (15 : ZMod 122314386981697) ^ 2602433765568 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (15 : ZMod 122314386981697) ^ 821184 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_129885093883087 : Nat.Prime 129885093883087 := by
  apply lucas_primality 129885093883087 (3 : ZMod 129885093883087)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (103, 1), (11061581833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (103, 1), (11061581833, 1)] : List FactorBlock).map factorBlockValue).prod) = 129885093883087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_103
      · exact prime_oneHundredCT_11061581833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 129885093883087) ^ 64942546941543 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 43295031294362 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 6836057572794 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 1261020328962 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 129885093883087) ^ 11742 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_138705063180113 : Nat.Prime 138705063180113 := by
  apply lucas_primality 138705063180113 (3 : ZMod 138705063180113)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) = 138705063180113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_3566049547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138705063180113) ^ 69352531590056 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 12609551198192 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 10669620244624 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 8159121363536 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 38896 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_139034446677491 : Nat.Prime 139034446677491 := by
  apply lucas_primality 139034446677491 (2 : ZMod 139034446677491)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) = 139034446677491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_443
      · exact prime_oneHundredCT_18151967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139034446677491) ^ 69517223338745 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 27806889335498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 19862063811070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 10694957436730 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7317602456710 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 313847509430 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7659470 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_148881354880871 : Nat.Prime 148881354880871 := by
  apply lucas_primality 148881354880871 (7 : ZMod 148881354880871)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (113, 1), (3213497839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (113, 1), (3213497839, 1)] : List FactorBlock).map factorBlockValue).prod) = 148881354880871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_41
      · exact prime_oneHundredCT_113
      · exact prime_oneHundredCT_3213497839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 148881354880871) ^ 74440677440435 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 148881354880871) ^ 29776270976174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 148881354880871) ^ 3631252558070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 148881354880871) ^ 1317534113990 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 148881354880871) ^ 46330 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_189964067570743 : Nat.Prime 189964067570743 := by
  apply lucas_primality 189964067570743 (3 : ZMod 189964067570743)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (53, 1), (179969, 1), (195253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (53, 1), (179969, 1), (195253, 1)] : List FactorBlock).map factorBlockValue).prod) = 189964067570743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_53
      · exact prime_oneHundredCT_179969
      · exact prime_oneHundredCT_195253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 189964067570743) ^ 94982033785371 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 63321355856914 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 11174356915926 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 3584227690014 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 1055537718 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 189964067570743) ^ 972912414 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_191204420330023 : Nat.Prime 191204420330023 := by
  apply lucas_primality 191204420330023 (3 : ZMod 191204420330023)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (107, 1), (27075109081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (107, 1), (27075109081, 1)] : List FactorBlock).map factorBlockValue).prod) = 191204420330023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_107
      · exact prime_oneHundredCT_27075109081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191204420330023) ^ 95602210165011 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 191204420330023) ^ 63734806776674 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 191204420330023) ^ 17382220030002 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 191204420330023) ^ 1786957199346 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 191204420330023) ^ 7062 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_194874783926681 : Nat.Prime 194874783926681 := by
  apply lucas_primality 194874783926681 (3 : ZMod 194874783926681)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) = 194874783926681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_17351
      · exact prime_oneHundredCT_41777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194874783926681) ^ 97437391963340 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 38974956785336 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 17715889447880 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 14990367994360 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4146271998440 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 11231328680 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4664642840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_197320078064177 : Nat.Prime 197320078064177 := by
  apply lucas_primality 197320078064177 (3 : ZMod 197320078064177)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) = 197320078064177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_1327
      · exact prime_oneHundredCT_4273
      · exact prime_oneHundredCT_2174941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197320078064177) ^ 98660039032088 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 148696366288 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 46178347312 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 90724336 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_219680568361127 : Nat.Prime 219680568361127 := by
  apply lucas_primality 219680568361127 (5 : ZMod 219680568361127)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (479, 1), (3259, 1), (963871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (479, 1), (3259, 1), (963871, 1)] : List FactorBlock).map factorBlockValue).prod) = 219680568361127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_73
      · exact prime_oneHundredCT_479
      · exact prime_oneHundredCT_3259
      · exact prime_oneHundredCT_963871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 219680568361127) ^ 109840284180563 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 219680568361127) ^ 3009322854262 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 219680568361127) ^ 458623315994 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 219680568361127) ^ 67407354514 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 219680568361127) ^ 227914906 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_229641230433047 : Nat.Prime 229641230433047 := by
  apply lucas_primality 229641230433047 (5 : ZMod 229641230433047)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (54449, 1), (29701037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (54449, 1), (29701037, 1)] : List FactorBlock).map factorBlockValue).prod) = 229641230433047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_54449
      · exact prime_oneHundredCT_29701037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 229641230433047) ^ 114820615216523 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 229641230433047) ^ 3234383527226 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 229641230433047) ^ 4217547254 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 229641230433047) ^ 7731758 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_239147013649849 : Nat.Prime 239147013649849 := by
  apply lucas_primality 239147013649849 (11 : ZMod 239147013649849)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (62303, 1), (159935459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (62303, 1), (159935459, 1)] : List FactorBlock).map factorBlockValue).prod) = 239147013649849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_62303
      · exact prime_oneHundredCT_159935459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 239147013649849) ^ 119573506824924 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 79715671216616 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 3838451016 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 239147013649849) ^ 1495272 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_247160427850559 : Nat.Prime 247160427850559 := by
  apply lucas_primality 247160427850559 (11 : ZMod 247160427850559)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2230759, 1), (2915699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2230759, 1), (2915699, 1)] : List FactorBlock).map factorBlockValue).prod) = 247160427850559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_2230759
      · exact prime_oneHundredCT_2915699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 247160427850559) ^ 123580213925279 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 247160427850559) ^ 13008443571082 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 247160427850559) ^ 110796562 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 247160427850559) ^ 84768842 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_247184120357417 : Nat.Prime 247184120357417 := by
  apply lucas_primality 247184120357417 (3 : ZMod 247184120357417)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (71191, 1), (3586907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (71191, 1), (3586907, 1)] : List FactorBlock).map factorBlockValue).prod) = 247184120357417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_71191
      · exact prime_oneHundredCT_3586907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 247184120357417) ^ 123592060178708 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 22471283668856 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 3472125976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 247184120357417) ^ 68912888 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_10789
      · exact prime_oneHundredCT_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_456215739524723 : Nat.Prime 456215739524723 := by
  apply lucas_primality 456215739524723 (2 : ZMod 456215739524723)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (7358318379431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (7358318379431, 1)] : List FactorBlock).map factorBlockValue).prod) = 456215739524723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_7358318379431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 456215739524723) ^ 228107869762361 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 456215739524723) ^ 14716636758862 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 456215739524723) ^ 62 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_527257545208661 : Nat.Prime 527257545208661 := by
  apply lucas_primality 527257545208661 (2 : ZMod 527257545208661)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (3766125322919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (3766125322919, 1)] : List FactorBlock).map factorBlockValue).prod) = 527257545208661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_3766125322919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 527257545208661) ^ 263628772604330 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 527257545208661) ^ 105451509041732 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 527257545208661) ^ 75322506458380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 527257545208661) ^ 140 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_766253565009377 : Nat.Prime 766253565009377 := by
  apply lucas_primality 766253565009377 (3 : ZMod 766253565009377)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) = 766253565009377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_11551
      · exact prime_oneHundredCT_90131191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 766253565009377) ^ 383126782504688 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 33315372391712 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 66336556576 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 8501536 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_806180877316877 : Nat.Prime 806180877316877 := by
  apply lucas_primality 806180877316877 (2 : ZMod 806180877316877)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (113, 1), (367, 1), (54605701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (113, 1), (367, 1), (54605701, 1)] : List FactorBlock).map factorBlockValue).prod) = 806180877316877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_89
      · exact prime_oneHundredCT_113
      · exact prime_oneHundredCT_367
      · exact prime_oneHundredCT_54605701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 806180877316877) ^ 403090438658438 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 806180877316877) ^ 9058212104684 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 806180877316877) ^ 7134344047052 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 806180877316877) ^ 2196678139828 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 806180877316877) ^ 14763676 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_847204358103163 : Nat.Prime 847204358103163 := by
  apply lucas_primality 847204358103163 (7 : ZMod 847204358103163)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (109, 1), (47978500289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (109, 1), (47978500289, 1)] : List FactorBlock).map factorBlockValue).prod) = 847204358103163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_109
      · exact prime_oneHundredCT_47978500289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 847204358103163) ^ 423602179051581 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 847204358103163) ^ 282401452701054 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 847204358103163) ^ 7772517046818 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 847204358103163) ^ 17658 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_873717055755871 : Nat.Prime 873717055755871 := by
  apply lucas_primality 873717055755871 (6 : ZMod 873717055755871)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (773, 1), (476917187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (773, 1), (476917187, 1)] : List FactorBlock).map factorBlockValue).prod) = 873717055755871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_79
      · exact prime_oneHundredCT_773
      · exact prime_oneHundredCT_476917187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 873717055755871) ^ 436858527877935 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 873717055755871) ^ 291239018585290 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 873717055755871) ^ 174743411151174 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 873717055755871) ^ 11059709566530 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 873717055755871) ^ 1130293733190 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 873717055755871) ^ 1832010 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1440715019131529 : Nat.Prime 1440715019131529 := by
  apply lucas_primality 1440715019131529 (3 : ZMod 1440715019131529)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (56893, 1), (452200691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (56893, 1), (452200691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440715019131529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_56893
      · exact prime_oneHundredCT_452200691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1440715019131529) ^ 720357509565764 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440715019131529) ^ 205816431304504 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440715019131529) ^ 25323238696 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1440715019131529) ^ 3186008 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1743791147825201 : Nat.Prime 1743791147825201 := by
  apply lucas_primality 1743791147825201 (7 : ZMod 1743791147825201)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (31, 1), (1667, 1), (84360119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (31, 1), (1667, 1), (84360119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1743791147825201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_1667
      · exact prime_oneHundredCT_84360119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1743791147825201) ^ 871895573912600 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743791147825201) ^ 348758229565040 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743791147825201) ^ 56251327349200 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743791147825201) ^ 1046065475600 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1743791147825201) ^ 20670800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2045753412374201 : Nat.Prime 2045753412374201 := by
  apply lucas_primality 2045753412374201 (6 : ZMod 2045753412374201)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (10228767061871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (10228767061871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2045753412374201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_10228767061871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2045753412374201) ^ 1022876706187100 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2045753412374201) ^ 409150682474840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 2045753412374201) ^ 200 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3141663309578149 : Nat.Prime 3141663309578149 := by
  apply lucas_primality 3141663309578149 (6 : ZMod 3141663309578149)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (733, 1), (357169544063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (733, 1), (357169544063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3141663309578149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_733
      · exact prime_oneHundredCT_357169544063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3141663309578149) ^ 1570831654789074 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 1047221103192716 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 4286034528756 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 8796 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3155852699721329 : Nat.Prime 3155852699721329 := by
  apply lucas_primality 3155852699721329 (3 : ZMod 3155852699721329)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (359, 1), (549417252737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (359, 1), (549417252737, 1)] : List FactorBlock).map factorBlockValue).prod) = 3155852699721329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_359
      · exact prime_oneHundredCT_549417252737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3155852699721329) ^ 1577926349860664 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3155852699721329) ^ 8790676043792 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3155852699721329) ^ 5744 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_3317807010514973 : Nat.Prime 3317807010514973 := by
  apply lucas_primality 3317807010514973 (2 : ZMod 3317807010514973)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (479, 1), (1731632051417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (479, 1), (1731632051417, 1)] : List FactorBlock).map factorBlockValue).prod) = 3317807010514973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_479
      · exact prime_oneHundredCT_1731632051417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3317807010514973) ^ 1658903505257486 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3317807010514973) ^ 6926528205668 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3317807010514973) ^ 1916 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_4613086018624079 : Nat.Prime 4613086018624079 := by
  apply lucas_primality 4613086018624079 (23 : ZMod 4613086018624079)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (1343356441067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (1343356441067, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613086018624079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_101
      · exact prime_oneHundredCT_1343356441067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 4613086018624079) ^ 2306543009312039 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 271358001095534 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 45674118996278 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (23 : ZMod 4613086018624079) ^ 3434 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_5066744382093707 : Nat.Prime 5066744382093707 := by
  apply lucas_primality 5066744382093707 (2 : ZMod 5066744382093707)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) = 5066744382093707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_194874783926681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5066744382093707) ^ 2533372191046853 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 389749567853362 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 26 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_8151940739207033 : Nat.Prime 8151940739207033 := by
  apply lucas_primality 8151940739207033 (3 : ZMod 8151940739207033)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151940739207033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_997
      · exact prime_oneHundredCT_1022058768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8151940739207033) ^ 4075970369603516 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 8176470149656 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 7976 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_18026111139253033 : Nat.Prime 18026111139253033 := by
  apply lucas_primality 18026111139253033 (5 : ZMod 18026111139253033)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (219979, 1), (3414362117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (219979, 1), (3414362117, 1)] : List FactorBlock).map factorBlockValue).prod) = 18026111139253033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_219979
      · exact prime_oneHundredCT_3414362117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18026111139253033) ^ 9013055569626516 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 6008703713084344 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 81944690808 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 18026111139253033) ^ 5279496 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_24193288987440403 : Nat.Prime 24193288987440403 := by
  apply lucas_primality 24193288987440403 (2 : ZMod 24193288987440403)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (15331615327909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (15331615327909, 1)] : List FactorBlock).map factorBlockValue).prod) = 24193288987440403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_263
      · exact prime_oneHundredCT_15331615327909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24193288987440403) ^ 12096644493720201 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 8064429662480134 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 91989691967454 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24193288987440403) ^ 1578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_28415877998359997 : Nat.Prime 28415877998359997 := by
  apply lucas_primality 28415877998359997 (2 : ZMod 28415877998359997)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4159, 1), (1708095575761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4159, 1), (1708095575761, 1)] : List FactorBlock).map factorBlockValue).prod) = 28415877998359997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_4159
      · exact prime_oneHundredCT_1708095575761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28415877998359997) ^ 14207938999179998 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28415877998359997) ^ 6832382303044 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 28415877998359997) ^ 16636 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_35191226542465943 : Nat.Prime 35191226542465943 := by
  apply lucas_primality 35191226542465943 (5 : ZMod 35191226542465943)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) = 35191226542465943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_28541
      · exact prime_oneHundredCT_47423310787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35191226542465943) ^ 17595613271232971 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 2707017426343534 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 1233006080462 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 742066 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_37870232396655949 : Nat.Prime 37870232396655949 := by
  apply lucas_primality 37870232396655949 (2 : ZMod 37870232396655949)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3155852699721329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3155852699721329, 1)] : List FactorBlock).map factorBlockValue).prod) = 37870232396655949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_3155852699721329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37870232396655949) ^ 18935116198327974 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 37870232396655949) ^ 12623410798885316 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 37870232396655949) ^ 12 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_39417317410818037 : Nat.Prime 39417317410818037 := by
  apply lucas_primality 39417317410818037 (2 : ZMod 39417317410818037)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (36907600571927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (36907600571927, 1)] : List FactorBlock).map factorBlockValue).prod) = 39417317410818037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_89
      · exact prime_oneHundredCT_36907600571927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39417317410818037) ^ 19708658705409018 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39417317410818037) ^ 13139105803606012 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39417317410818037) ^ 442891206863124 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39417317410818037) ^ 1068 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_46107020391770753 : Nat.Prime 46107020391770753 := by
  apply lucas_primality 46107020391770753 (3 : ZMod 46107020391770753)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (19, 1), (617, 1), (30726869983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (19, 1), (617, 1), (30726869983, 1)] : List FactorBlock).map factorBlockValue).prod) = 46107020391770753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_617
      · exact prime_oneHundredCT_30726869983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46107020391770753) ^ 23053510195885376 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46107020391770753) ^ 2426685283777408 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46107020391770753) ^ 74727747798656 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46107020391770753) ^ 1500544 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_53015135238325067 : Nat.Prime 53015135238325067 := by
  apply lucas_primality 53015135238325067 (2 : ZMod 53015135238325067)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) = 53015135238325067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_163
      · exact prime_oneHundredCT_9566065542823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53015135238325067) ^ 26507567619162533 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 3118537366960298 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 325246228455982 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 5542 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_139
      · exact prime_oneHundredCT_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_68731006467186887 : Nat.Prime 68731006467186887 := by
  apply lucas_primality 68731006467186887 (5 : ZMod 68731006467186887)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (71, 1), (1674813744997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (71, 1), (1674813744997, 1)] : List FactorBlock).map factorBlockValue).prod) = 68731006467186887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_1674813744997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 68731006467186887) ^ 34365503233593443 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68731006467186887) ^ 4043000380422758 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68731006467186887) ^ 968042344608266 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68731006467186887) ^ 41038 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_90271424483937779 : Nat.Prime 90271424483937779 := by
  apply lucas_primality 90271424483937779 (2 : ZMod 90271424483937779)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) = 90271424483937779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_131
      · exact prime_oneHundredCT_771643
      · exact prime_oneHundredCT_446511433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90271424483937779) ^ 45135712241968889 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 689094843388838 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 116985995446 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 202170466 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_91950427801125241 : Nat.Prime 91950427801125241 := by
  apply lucas_primality 91950427801125241 (14 : ZMod 91950427801125241)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) = 91950427801125241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_766253565009377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 91950427801125241) ^ 45975213900562620 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 30650142600375080 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 18390085560225048 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 120 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_92214040783541507 : Nat.Prime 92214040783541507 := by
  apply lucas_primality 92214040783541507 (2 : ZMod 92214040783541507)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46107020391770753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46107020391770753, 1)] : List FactorBlock).map factorBlockValue).prod) = 92214040783541507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_46107020391770753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 92214040783541507) ^ 46107020391770753 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 92214040783541507) ^ 2 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_101506984564892419 : Nat.Prime 101506984564892419 := by
  apply lucas_primality 101506984564892419 (3 : ZMod 101506984564892419)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1693, 1), (3330937342157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1693, 1), (3330937342157, 1)] : List FactorBlock).map factorBlockValue).prod) = 101506984564892419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1693
      · exact prime_oneHundredCT_3330937342157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101506984564892419) ^ 50753492282446209 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 33835661521630806 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 59956872158826 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 101506984564892419) ^ 30474 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_117461778302995013 : Nat.Prime 117461778302995013 := by
  apply lucas_primality 117461778302995013 (2 : ZMod 117461778302995013)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14683, 1), (39451, 1), (50694841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14683, 1), (39451, 1), (50694841, 1)] : List FactorBlock).map factorBlockValue).prod) = 117461778302995013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_14683
      · exact prime_oneHundredCT_39451
      · exact prime_oneHundredCT_50694841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117461778302995013) ^ 58730889151497506 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117461778302995013) ^ 7999848689164 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117461778302995013) ^ 2977409401612 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 117461778302995013) ^ 2317036132 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_153535346828908273 : Nat.Prime 153535346828908273 := by
  apply lucas_primality 153535346828908273 (5 : ZMod 153535346828908273)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (101, 1), (10556610755563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (101, 1), (10556610755563, 1)] : List FactorBlock).map factorBlockValue).prod) = 153535346828908273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_101
      · exact prime_oneHundredCT_10556610755563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 153535346828908273) ^ 76767673414454136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 153535346828908273) ^ 51178448942969424 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 153535346828908273) ^ 1520151948801072 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 153535346828908273) ^ 14544 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_158812959932849581 : Nat.Prime 158812959932849581 := by
  apply lucas_primality 158812959932849581 (2 : ZMod 158812959932849581)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (59, 1), (997, 1), (44997410291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (59, 1), (997, 1), (44997410291, 1)] : List FactorBlock).map factorBlockValue).prod) = 158812959932849581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_59
      · exact prime_oneHundredCT_997
      · exact prime_oneHundredCT_44997410291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158812959932849581) ^ 79406479966424790 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 52937653310949860 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 31762591986569916 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 2691745083607620 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 159290832430140 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158812959932849581) ^ 3529380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_161555159326910779 : Nat.Prime 161555159326910779 := by
  apply lucas_primality 161555159326910779 (2 : ZMod 161555159326910779)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (13, 1), (1889, 1), (11075391241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (13, 1), (1889, 1), (11075391241, 1)] : List FactorBlock).map factorBlockValue).prod) = 161555159326910779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_1889
      · exact prime_oneHundredCT_11075391241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161555159326910779) ^ 80777579663455389 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 53851719775636926 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 14686832666082798 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 12427319948223906 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 85524171163002 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 161555159326910779) ^ 14586858 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_258268827641370407 : Nat.Prime 258268827641370407 := by
  apply lucas_primality 258268827641370407 (7 : ZMod 258268827641370407)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) = 258268827641370407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_138705063180113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 258268827641370407) ^ 129134413820685203 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 36895546805910058 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 13593096191651074 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 1862 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_564728604530869829 : Nat.Prime 564728604530869829 := by
  apply lucas_primality 564728604530869829 (2 : ZMod 564728604530869829)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (291721, 1), (69137562031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (291721, 1), (69137562031, 1)] : List FactorBlock).map factorBlockValue).prod) = 564728604530869829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_291721
      · exact prime_oneHundredCT_69137562031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 564728604530869829) ^ 282364302265434914 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 564728604530869829) ^ 80675514932981404 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 564728604530869829) ^ 1935851736868 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 564728604530869829) ^ 8168188 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_654674757345372251 : Nat.Prime 654674757345372251 := by
  apply lucas_primality 654674757345372251 (2 : ZMod 654674757345372251)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (586741, 1), (4463126029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (586741, 1), (4463126029, 1)] : List FactorBlock).map factorBlockValue).prod) = 654674757345372251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_586741
      · exact prime_oneHundredCT_4463126029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 654674757345372251) ^ 327337378672686125 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 654674757345372251) ^ 130934951469074450 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 654674757345372251) ^ 1115781507250 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 654674757345372251) ^ 146685250 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1095765587763403201 : Nat.Prime 1095765587763403201 := by
  apply lucas_primality 1095765587763403201 (11 : ZMod 1095765587763403201)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 1), (59, 1), (167, 1), (3209, 1), (1031431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 1), (59, 1), (167, 1), (3209, 1), (1031431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1095765587763403201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_59
      · exact prime_oneHundredCT_167
      · exact prime_oneHundredCT_3209
      · exact prime_oneHundredCT_1031431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1095765587763403201) ^ 547882793881701600 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 365255195921134400 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 219153117552680640 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 156537941109057600 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 18572298097684800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 6561470585409600 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 341466372004800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1095765587763403201) ^ 1062374107200 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2108574390836795111 : Nat.Prime 2108574390836795111 := by
  apply lucas_primality 2108574390836795111 (17 : ZMod 2108574390836795111)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (11059, 1), (615051349459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (11059, 1), (615051349459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2108574390836795111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_11059
      · exact prime_oneHundredCT_615051349459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2108574390836795111) ^ 1054287195418397555 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 421714878167359022 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 68018528736670810 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 190665918332290 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 2108574390836795111) ^ 3428290 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_101
      · exact prime_oneHundredCT_191
      · exact prime_oneHundredCT_48017
      · exact prime_oneHundredCT_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2410219617571552777 : Nat.Prime 2410219617571552777 := by
  apply lucas_primality 2410219617571552777 (10 : ZMod 2410219617571552777)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410219617571552777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_10223538369013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2410219617571552777) ^ 1205109808785776388 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 803406539190517592 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 219110874324686616 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 126853664082713304 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 51281268458969208 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 235752 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_4421305627276911211 : Nat.Prime 4421305627276911211 := by
  apply lucas_primality 4421305627276911211 (2 : ZMod 4421305627276911211)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (47, 1), (1931051, 1), (20047151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (47, 1), (1931051, 1), (20047151, 1)] : List FactorBlock).map factorBlockValue).prod) = 4421305627276911211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_47
      · exact prime_oneHundredCT_1931051
      · exact prime_oneHundredCT_20047151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4421305627276911211) ^ 2210652813638455605 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4421305627276911211) ^ 1473768542425637070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4421305627276911211) ^ 884261125455382242 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4421305627276911211) ^ 94070332495253430 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4421305627276911211) ^ 2289585115710 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4421305627276911211) ^ 220545334710 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_14461317705429316663 : Nat.Prime 14461317705429316663 := by
  apply lucas_primality 14461317705429316663 (3 : ZMod 14461317705429316663)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) = 14461317705429316663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2410219617571552777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14461317705429316663) ^ 7230658852714658331 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 4820439235143105554 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 6 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_19096906877256609199 : Nat.Prime 19096906877256609199 := by
  apply lucas_primality 19096906877256609199 (6 : ZMod 19096906877256609199)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) = 19096906877256609199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_53
      · exact prime_oneHundredCT_6697657
      · exact prime_oneHundredCT_426966413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19096906877256609199) ^ 9548453438628304599 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 6365635625752203066 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2728129553893801314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 360318997684086966 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2851281706014 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 44726953446 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_22349259175745505109 : Nat.Prime 22349259175745505109 := by
  apply lucas_primality 22349259175745505109 (2 : ZMod 22349259175745505109)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (3869501, 1), (68758894037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (3869501, 1), (68758894037, 1)] : List FactorBlock).map factorBlockValue).prod) = 22349259175745505109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_3869501
      · exact prime_oneHundredCT_68758894037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22349259175745505109) ^ 11174629587872752554 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22349259175745505109) ^ 7449753058581835036 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22349259175745505109) ^ 3192751310820786444 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22349259175745505109) ^ 5775747099108 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22349259175745505109) ^ 325038084 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_33622691112624143459 : Nat.Prime 33622691112624143459 := by
  apply lucas_primality 33622691112624143459 (2 : ZMod 33622691112624143459)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (3853, 1), (229641230433047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (3853, 1), (229641230433047, 1)] : List FactorBlock).map factorBlockValue).prod) = 33622691112624143459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_3853
      · exact prime_oneHundredCT_229641230433047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33622691112624143459) ^ 16811345556312071729 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 33622691112624143459) ^ 1769615321717060182 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 33622691112624143459) ^ 8726366756455786 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 33622691112624143459) ^ 146414 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_37600086952193652409 : Nat.Prime 37600086952193652409 := by
  apply lucas_primality 37600086952193652409 (7 : ZMod 37600086952193652409)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6039659, 1), (259397143063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6039659, 1), (259397143063, 1)] : List FactorBlock).map factorBlockValue).prod) = 37600086952193652409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_6039659
      · exact prime_oneHundredCT_259397143063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37600086952193652409) ^ 18800043476096826204 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 12533362317397884136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 6225531433512 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 37600086952193652409) ^ 144951816 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_40918864317638395681 : Nat.Prime 40918864317638395681 := by
  apply lucas_primality 40918864317638395681 (7 : ZMod 40918864317638395681)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (28415877998359997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (28415877998359997, 1)] : List FactorBlock).map factorBlockValue).prod) = 40918864317638395681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_28415877998359997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 40918864317638395681) ^ 20459432158819197840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 40918864317638395681) ^ 13639621439212798560 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 40918864317638395681) ^ 8183772863527679136 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 40918864317638395681) ^ 1440 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_47971998361640878079 : Nat.Prime 47971998361640878079 := by
  apply lucas_primality 47971998361640878079 (7 : ZMod 47971998361640878079)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (203417, 1), (117915411105367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (203417, 1), (117915411105367, 1)] : List FactorBlock).map factorBlockValue).prod) = 47971998361640878079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_203417
      · exact prime_oneHundredCT_117915411105367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 47971998361640878079) ^ 23985999180820439039 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971998361640878079) ^ 235830822210734 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47971998361640878079) ^ 406834 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_2063
      · exact prime_oneHundredCT_15269
      · exact prime_oneHundredCT_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_58417921725750607099 : Nat.Prime 58417921725750607099 := by
  apply lucas_primality 58417921725750607099 (2 : ZMod 58417921725750607099)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3917, 1), (191204420330023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3917, 1), (191204420330023, 1)] : List FactorBlock).map factorBlockValue).prod) = 58417921725750607099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_3917
      · exact prime_oneHundredCT_191204420330023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58417921725750607099) ^ 29208960862875303549 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58417921725750607099) ^ 19472640575250202366 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58417921725750607099) ^ 4493686286596200546 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58417921725750607099) ^ 14913944785741794 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58417921725750607099) ^ 305526 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_98102383559288524519 : Nat.Prime 98102383559288524519 := by
  apply lucas_primality 98102383559288524519 (3 : ZMod 98102383559288524519)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (61, 1), (83, 1), (189964067570743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (61, 1), (83, 1), (189964067570743, 1)] : List FactorBlock).map factorBlockValue).prod) = 98102383559288524519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_61
      · exact prime_oneHundredCT_83
      · exact prime_oneHundredCT_189964067570743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 98102383559288524519) ^ 49051191779644262259 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 32700794519762841506 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 5770728444664030854 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 1608235796053910238 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 1181956428425162946 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 98102383559288524519) ^ 516426 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_177769765424490849629 : Nat.Prime 177769765424490849629 := by
  apply lucas_primality 177769765424490849629 (2 : ZMod 177769765424490849629)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (49499, 1), (28962749561003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (49499, 1), (28962749561003, 1)] : List FactorBlock).map factorBlockValue).prod) = 177769765424490849629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_49499
      · exact prime_oneHundredCT_28962749561003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 177769765424490849629) ^ 88884882712245424814 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 177769765424490849629) ^ 5734508562080349988 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 177769765424490849629) ^ 3591380945564372 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 177769765424490849629) ^ 6137876 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_241379296820428958299 : Nat.Prime 241379296820428958299 := by
  apply lucas_primality 241379296820428958299 (2 : ZMod 241379296820428958299)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61043, 1), (219680568361127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61043, 1), (219680568361127, 1)] : List FactorBlock).map factorBlockValue).prod) = 241379296820428958299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_61043
      · exact prime_oneHundredCT_219680568361127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 241379296820428958299) ^ 120689648410214479149 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 241379296820428958299) ^ 80459765606809652766 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 241379296820428958299) ^ 3954250230500286 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 241379296820428958299) ^ 1098774 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_396955775981747657419 : Nat.Prime 396955775981747657419 := by
  apply lucas_primality 396955775981747657419 (2 : ZMod 396955775981747657419)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1747, 1), (37870232396655949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1747, 1), (37870232396655949, 1)] : List FactorBlock).map factorBlockValue).prod) = 396955775981747657419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_1747
      · exact prime_oneHundredCT_37870232396655949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 396955775981747657419) ^ 198477887990873828709 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 396955775981747657419) ^ 132318591993915885806 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 396955775981747657419) ^ 227221394379935694 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 396955775981747657419) ^ 10482 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_695450024211916627019 : Nat.Prime 695450024211916627019 := by
  apply lucas_primality 695450024211916627019 (2 : ZMod 695450024211916627019)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) = 695450024211916627019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_2500999
      · exact prime_oneHundredCT_139034446677491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695450024211916627019) ^ 347725012105958313509 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 278068893354982 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 5001998 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_877597476325376642987 : Nat.Prime 877597476325376642987 := by
  apply lucas_primality 877597476325376642987 (2 : ZMod 877597476325376642987)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) = 877597476325376642987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_1699
      · exact prime_oneHundredCT_258268827641370407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 877597476325376642987) ^ 438798738162688321493 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 516537655282740814 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 3398 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_945822852012035820923 : Nat.Prime 945822852012035820923 := by
  apply lucas_primality 945822852012035820923 (5 : ZMod 945822852012035820923)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (11813, 1), (23227, 1), (3643890707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (11813, 1), (23227, 1), (3643890707, 1)] : List FactorBlock).map factorBlockValue).prod) = 945822852012035820923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_11813
      · exact prime_oneHundredCT_23227
      · exact prime_oneHundredCT_3643890707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 945822852012035820923) ^ 472911426006017910461 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 945822852012035820923) ^ 85983895637457801902 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 945822852012035820923) ^ 21995880279349670254 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 945822852012035820923) ^ 80066270381108594 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 945822852012035820923) ^ 40720835752014286 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 945822852012035820923) ^ 259564001246 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_71
      · exact prime_oneHundredCT_199
      · exact prime_oneHundredCT_52864081
      · exact prime_oneHundredCT_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2114421171413953430767 : Nat.Prime 2114421171413953430767 := by
  apply lucas_primality 2114421171413953430767 (3 : ZMod 2114421171413953430767)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (10133, 1), (2045753412374201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (10133, 1), (2045753412374201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2114421171413953430767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_10133
      · exact prime_oneHundredCT_2045753412374201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2114421171413953430767) ^ 1057210585706976715383 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114421171413953430767) ^ 704807057137984476922 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114421171413953430767) ^ 124377715965526672398 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114421171413953430767) ^ 208666848062168502 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114421171413953430767) ^ 1033566 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2307642263509371299503 : Nat.Prime 2307642263509371299503 := by
  apply lucas_primality 2307642263509371299503 (5 : ZMod 2307642263509371299503)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2307642263509371299503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_31
      · exact prime_oneHundredCT_59
      · exact prime_oneHundredCT_77041
      · exact prime_oneHundredCT_2729490688553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2307642263509371299503) ^ 1153821131754685649751 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 769214087836457099834 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 74440073016431332242 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 39112580737446971178 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 29953430816180622 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 845447934 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6477408066238858455719 : Nat.Prime 6477408066238858455719 := by
  apply lucas_primality 6477408066238858455719 (11 : ZMod 6477408066238858455719)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14797, 1), (3441829, 1), (5781168313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14797, 1), (3441829, 1), (5781168313, 1)] : List FactorBlock).map factorBlockValue).prod) = 6477408066238858455719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_14797
      · exact prime_oneHundredCT_3441829
      · exact prime_oneHundredCT_5781168313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6477408066238858455719) ^ 3238704033119429227859 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 6477408066238858455719) ^ 588855278748987132338 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 6477408066238858455719) ^ 437751440578418494 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 6477408066238858455719) ^ 1881966845604142 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 6477408066238858455719) ^ 1120432361686 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_7389175414818054990001 : Nat.Prime 7389175414818054990001 := by
  apply lucas_primality 7389175414818054990001 (17 : ZMod 7389175414818054990001)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389175414818054990001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_433
      · exact prime_oneHundredCT_51712334066891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7389175414818054990001) ^ 3694587707409027495000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 2463058471606018330000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 1477835082963610998000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 671743219528914090000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 17065070242074030000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 142890000 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_13256972514058216452869 : Nat.Prime 13256972514058216452869 := by
  apply lucas_primality 13256972514058216452869 (2 : ZMod 13256972514058216452869)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) = 13256972514058216452869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_82829821
      · exact prime_oneHundredCT_40012680077077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13256972514058216452869) ^ 6628486257029108226434 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 160050720308308 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 331319284 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_13737519737159276350811 : Nat.Prime 13737519737159276350811 := by
  apply lucas_primality 13737519737159276350811 (2 : ZMod 13737519737159276350811)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (62467, 1), (3141663309578149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (62467, 1), (3141663309578149, 1)] : List FactorBlock).map factorBlockValue).prod) = 13737519737159276350811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_62467
      · exact prime_oneHundredCT_3141663309578149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13737519737159276350811) ^ 6868759868579638175405 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 2747503947431855270162 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 1962502819594182335830 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 219916431670470430 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 4372690 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_16818143506935383652491 : Nat.Prime 16818143506935383652491 := by
  apply lucas_primality 16818143506935383652491 (2 : ZMod 16818143506935383652491)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1699, 1), (159007399, 1), (565945559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1699, 1), (159007399, 1), (565945559, 1)] : List FactorBlock).map factorBlockValue).prod) = 16818143506935383652491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_1699
      · exact prime_oneHundredCT_159007399
      · exact prime_oneHundredCT_565945559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16818143506935383652491) ^ 8409071753467691826245 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 16818143506935383652491) ^ 3363628701387076730498 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 16818143506935383652491) ^ 1528922136994125786590 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 16818143506935383652491) ^ 9898848444341014510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 16818143506935383652491) ^ 105769565521510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 16818143506935383652491) ^ 29716892799110 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_22533477323856334956979 : Nat.Prime 22533477323856334956979 := by
  apply lucas_primality 22533477323856334956979 (2 : ZMod 22533477323856334956979)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (18229, 1), (1440715019131529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (18229, 1), (1440715019131529, 1)] : List FactorBlock).map factorBlockValue).prod) = 22533477323856334956979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_18229
      · exact prime_oneHundredCT_1440715019131529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22533477323856334956979) ^ 11266738661928167478489 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533477323856334956979) ^ 7511159107952111652326 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533477323856334956979) ^ 2048497938532394086998 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533477323856334956979) ^ 1733344409527410381306 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533477323856334956979) ^ 1236133486414851882 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533477323856334956979) ^ 15640482 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_22764944433009774922687 : Nat.Prime 22764944433009774922687 := by
  apply lucas_primality 22764944433009774922687 (3 : ZMod 22764944433009774922687)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24121994333, 1), (52430123219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24121994333, 1), (52430123219, 1)] : List FactorBlock).map factorBlockValue).prod) = 22764944433009774922687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_24121994333
      · exact prime_oneHundredCT_52430123219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22764944433009774922687) ^ 11382472216504887461343 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 22764944433009774922687) ^ 7588314811003258307562 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 22764944433009774922687) ^ 943742217942 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 22764944433009774922687) ^ 434195897994 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_37722715885170866626103 : Nat.Prime 37722715885170866626103 := by
  apply lucas_primality 37722715885170866626103 (5 : ZMod 37722715885170866626103)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (19013, 1), (3317807010514973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (19013, 1), (3317807010514973, 1)] : List FactorBlock).map factorBlockValue).prod) = 37722715885170866626103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_19013
      · exact prime_oneHundredCT_3317807010514973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37722715885170866626103) ^ 18861357942585433313051 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37722715885170866626103) ^ 2901747375782374355854 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37722715885170866626103) ^ 1640118081963950722874 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37722715885170866626103) ^ 1984048592287953854 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 37722715885170866626103) ^ 11369774 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_38788105438584679319431 : Nat.Prime 38788105438584679319431 := by
  apply lucas_primality 38788105438584679319431 (3 : ZMod 38788105438584679319431)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2834047, 1), (456215739524723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2834047, 1), (456215739524723, 1)] : List FactorBlock).map factorBlockValue).prod) = 38788105438584679319431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_2834047
      · exact prime_oneHundredCT_456215739524723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38788105438584679319431) ^ 19394052719292339659715 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 12929368479528226439810 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 7757621087716935863886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 13686472185741690 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 38788105438584679319431) ^ 85021410 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_95538030348927817797203 : Nat.Prime 95538030348927817797203 := by
  apply lucas_primality 95538030348927817797203 (2 : ZMod 95538030348927817797203)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (113, 1), (409, 1), (1117, 1), (7775787827411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (113, 1), (409, 1), (1117, 1), (7775787827411, 1)] : List FactorBlock).map factorBlockValue).prod) = 95538030348927817797203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_113
      · exact prime_oneHundredCT_409
      · exact prime_oneHundredCT_1117
      · exact prime_oneHundredCT_7775787827411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95538030348927817797203) ^ 47769015174463908898601 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 13648290049846831113886 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 5619884138172224576306 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 845469295123255024754 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 233589316256547231778 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 85530913472630096506 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 95538030348927817797203) ^ 12286604582 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_136589666598058649536123 : Nat.Prime 136589666598058649536123 := by
  apply lucas_primality 136589666598058649536123 (2 : ZMod 136589666598058649536123)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22764944433009774922687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22764944433009774922687, 1)] : List FactorBlock).map factorBlockValue).prod) = 136589666598058649536123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_22764944433009774922687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 136589666598058649536123) ^ 68294833299029324768061 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 136589666598058649536123) ^ 45529888866019549845374 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 136589666598058649536123) ^ 6 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_144106307933055964192591 : Nat.Prime 144106307933055964192591 := by
  apply lucas_primality 144106307933055964192591 (3 : ZMod 144106307933055964192591)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (92889289, 1), (407185568351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (92889289, 1), (407185568351, 1)] : List FactorBlock).map factorBlockValue).prod) = 144106307933055964192591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_127
      · exact prime_oneHundredCT_92889289
      · exact prime_oneHundredCT_407185568351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144106307933055964192591) ^ 72053153966527982096295 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 144106307933055964192591) ^ 48035435977685321397530 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 144106307933055964192591) ^ 28821261586611192838518 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 144106307933055964192591) ^ 1134695338055558773170 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 144106307933055964192591) ^ 1551377015417310 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 144106307933055964192591) ^ 353908191090 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_165038784307659787998353 : Nat.Prime 165038784307659787998353 := by
  apply lucas_primality 165038784307659787998353 (3 : ZMod 165038784307659787998353)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (23, 1), (61, 1), (6113, 1), (5230997, 1), (20901469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (23, 1), (61, 1), (6113, 1), (5230997, 1), (20901469, 1)] : List FactorBlock).map factorBlockValue).prod) = 165038784307659787998353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_61
      · exact prime_oneHundredCT_6113
      · exact prime_oneHundredCT_5230997
      · exact prime_oneHundredCT_20901469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 165038784307659787998353) ^ 82519392153829893999176 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 15003525846150889818032 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 7175599317724338608624 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 2705553841109176852432 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 26998001686186780304 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 31550158470299216 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 165038784307659787998353) ^ 7896037561171408 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_446811192740323138427807 : Nat.Prime 446811192740323138427807 := by
  apply lucas_primality 446811192740323138427807 (5 : ZMod 446811192740323138427807)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4657, 1), (47971998361640878079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4657, 1), (47971998361640878079, 1)] : List FactorBlock).map factorBlockValue).prod) = 446811192740323138427807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_4657
      · exact prime_oneHundredCT_47971998361640878079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 446811192740323138427807) ^ 223405596370161569213903 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 446811192740323138427807) ^ 95943996723281756158 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 446811192740323138427807) ^ 9314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_553814642374973616601021 : Nat.Prime 553814642374973616601021 := by
  apply lucas_primality 553814642374973616601021 (2 : ZMod 553814642374973616601021)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (59, 1), (22349259175745505109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (59, 1), (22349259175745505109, 1)] : List FactorBlock).map factorBlockValue).prod) = 553814642374973616601021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_59
      · exact prime_oneHundredCT_22349259175745505109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 553814642374973616601021) ^ 276907321187486808300510 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 553814642374973616601021) ^ 184604880791657872200340 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 553814642374973616601021) ^ 110762928474994723320204 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 553814642374973616601021) ^ 79116377482139088085860 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 553814642374973616601021) ^ 9386688853813112145780 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 553814642374973616601021) ^ 24780 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_558426407371653470016797 : Nat.Prime 558426407371653470016797 := by
  apply lucas_primality 558426407371653470016797 (2 : ZMod 558426407371653470016797)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (463, 1), (2108574390836795111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (463, 1), (2108574390836795111, 1)] : List FactorBlock).map factorBlockValue).prod) = 558426407371653470016797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_463
      · exact prime_oneHundredCT_2108574390836795111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 558426407371653470016797) ^ 279213203685826735008398 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 50766037033786679092436 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 42955877490127190001292 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 1206104551558646803492 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 558426407371653470016797) ^ 264836 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_617594268484635418250629 : Nat.Prime 617594268484635418250629 := by
  apply lucas_primality 617594268484635418250629 (6 : ZMod 617594268484635418250629)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (881, 1), (58417921725750607099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (881, 1), (58417921725750607099, 1)] : List FactorBlock).map factorBlockValue).prod) = 617594268484635418250629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_881
      · exact prime_oneHundredCT_58417921725750607099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 617594268484635418250629) ^ 308797134242317709125314 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 617594268484635418250629) ^ 205864756161545139416876 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 617594268484635418250629) ^ 701015060709007285188 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 617594268484635418250629) ^ 10572 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_700038418875941420550763 : Nat.Prime 700038418875941420550763 := by
  apply lucas_primality 700038418875941420550763 (2 : ZMod 700038418875941420550763)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (107, 1), (37600086952193652409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (107, 1), (37600086952193652409, 1)] : List FactorBlock).map factorBlockValue).prod) = 700038418875941420550763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_107
      · exact prime_oneHundredCT_37600086952193652409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 700038418875941420550763) ^ 350019209437970710275381 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 233346139625313806850254 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 24139255823308324846578 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 6542415129681695519166 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 700038418875941420550763) ^ 18618 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_714520396767145783354201 : Nat.Prime 714520396767145783354201 := by
  apply lucas_primality 714520396767145783354201 (11 : ZMod 714520396767145783354201)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (396955775981747657419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (396955775981747657419, 1)] : List FactorBlock).map factorBlockValue).prod) = 714520396767145783354201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_396955775981747657419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 714520396767145783354201) ^ 357260198383572891677100 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714520396767145783354201) ^ 238173465589048594451400 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714520396767145783354201) ^ 142904079353429156670840 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714520396767145783354201) ^ 1800 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_810110309172203747806523 : Nat.Prime 810110309172203747806523 := by
  apply lucas_primality 810110309172203747806523 (2 : ZMod 810110309172203747806523)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (56511551, 1), (247160427850559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (56511551, 1), (247160427850559, 1)] : List FactorBlock).map factorBlockValue).prod) = 810110309172203747806523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_29
      · exact prime_oneHundredCT_56511551
      · exact prime_oneHundredCT_247160427850559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 810110309172203747806523) ^ 405055154586101873903261 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810110309172203747806523) ^ 27934838247317370614018 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810110309172203747806523) ^ 14335304815332422 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810110309172203747806523) ^ 3277669958 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_818954222413514839336507 : Nat.Prime 818954222413514839336507 := by
  apply lucas_primality 818954222413514839336507 (3 : ZMod 818954222413514839336507)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 2), (4671137, 1), (80942864418343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 2), (4671137, 1), (80942864418343, 1)] : List FactorBlock).map factorBlockValue).prod) = 818954222413514839336507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_4671137
      · exact prime_oneHundredCT_80942864418343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 818954222413514839336507) ^ 409477111206757419668253 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 818954222413514839336507) ^ 272984740804504946445502 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 818954222413514839336507) ^ 43102853811237623122974 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 818954222413514839336507) ^ 175322244330130938 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 818954222413514839336507) ^ 10117682742 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_1093304682118814492274949 : Nat.Prime 1093304682118814492274949 := by
  apply lucas_primality 1093304682118814492274949 (6 : ZMod 1093304682118814492274949)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (11, 1), (13, 1), (23, 1), (173, 1), (847204358103163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (11, 1), (13, 1), (23, 1), (173, 1), (847204358103163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1093304682118814492274949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_173
      · exact prime_oneHundredCT_847204358103163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1093304682118814492274949) ^ 546652341059407246137474 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 364434894039604830758316 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 156186383159830641753564 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 99391334738074044752268 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 84100360162985730174996 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 47534986179078890968476 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 6319680243461355446676 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1093304682118814492274949) ^ 1290485196 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2072770581196434705830081 : Nat.Prime 2072770581196434705830081 := by
  apply lucas_primality 2072770581196434705830081 (3 : ZMod 2072770581196434705830081)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (6477408066238858455719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (6477408066238858455719, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072770581196434705830081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_6477408066238858455719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2072770581196434705830081) ^ 1036385290598217352915040 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072770581196434705830081) ^ 414554116239286941166016 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2072770581196434705830081) ^ 320 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2884351616538150302547907 : Nat.Prime 2884351616538150302547907 := by
  apply lucas_primality 2884351616538150302547907 (3 : ZMod 2884351616538150302547907)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11329, 1), (11497, 1), (527257545208661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11329, 1), (11497, 1), (527257545208661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2884351616538150302547907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11329
      · exact prime_oneHundredCT_11497
      · exact prime_oneHundredCT_527257545208661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2884351616538150302547907) ^ 1442175808269075151273953 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884351616538150302547907) ^ 961450538846050100849302 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884351616538150302547907) ^ 412050230934021471792558 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884351616538150302547907) ^ 254598959885086971714 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884351616538150302547907) ^ 250878630646094659698 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2884351616538150302547907) ^ 5470479546 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_5366865877265524660726141 : Nat.Prime 5366865877265524660726141 := by
  apply lucas_primality 5366865877265524660726141 (2 : ZMod 5366865877265524660726141)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 1), (257, 1), (750983, 1), (5721649413079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 1), (257, 1), (750983, 1), (5721649413079, 1)] : List FactorBlock).map factorBlockValue).prod) = 5366865877265524660726141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_257
      · exact prime_oneHundredCT_750983
      · exact prime_oneHundredCT_5721649413079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5366865877265524660726141) ^ 2683432938632762330363070 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5366865877265524660726141) ^ 1788955292421841553575380 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5366865877265524660726141) ^ 1073373175453104932145228 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5366865877265524660726141) ^ 20882746604146010353020 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5366865877265524660726141) ^ 7146454549923932580 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5366865877265524660726141) ^ 937992786660 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_6861676634375057617593509 : Nat.Prime 6861676634375057617593509 := by
  apply lucas_primality 6861676634375057617593509 (2 : ZMod 6861676634375057617593509)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6861676634375057617593509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_210430769
      · exact prime_oneHundredCT_8151940739207033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6861676634375057617593509) ^ 3430838317187528808796754 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 32607762956828132 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 841723076 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_8268757057650177839637443 : Nat.Prime 8268757057650177839637443 := by
  apply lucas_primality 8268757057650177839637443 (2 : ZMod 8268757057650177839637443)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (3463, 1), (1090151, 1), (2800878888487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (3463, 1), (1090151, 1), (2800878888487, 1)] : List FactorBlock).map factorBlockValue).prod) = 8268757057650177839637443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_17
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_3463
      · exact prime_oneHundredCT_1090151
      · exact prime_oneHundredCT_2800878888487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8268757057650177839637443) ^ 4134378528825088919818721 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 486397473979422225861026 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 359511176419572949549454 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 2387743880349459381934 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 7584964888029436142 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268757057650177839637443) ^ 2952200857966 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_110389064808853634688269057 : Nat.Prime 110389064808853634688269057 := by
  apply lucas_primality 110389064808853634688269057 (3 : ZMod 110389064808853634688269057)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7, 1), (19, 1), (43, 1), (6481, 1), (700307, 1), (16612519487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7, 1), (19, 1), (43, 1), (6481, 1), (700307, 1), (16612519487, 1)] : List FactorBlock).map factorBlockValue).prod) = 110389064808853634688269057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_19
      · exact prime_oneHundredCT_43
      · exact prime_oneHundredCT_6481
      · exact prime_oneHundredCT_700307
      · exact prime_oneHundredCT_16612519487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 110389064808853634688269057) ^ 55194532404426817344134528 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 15769866401264804955467008 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 5809950779413349194119424 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 2567187553694270574145792 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 17032721001211793656576 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 157629532203524503808 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 110389064808853634688269057) ^ 6644932148626688 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_169622221535555585008803673 : Nat.Prime 169622221535555585008803673 := by
  apply lucas_primality 169622221535555585008803673 (7 : ZMod 169622221535555585008803673)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (83, 1), (479, 1), (177769765424490849629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (83, 1), (479, 1), (177769765424490849629, 1)] : List FactorBlock).map factorBlockValue).prod) = 169622221535555585008803673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_83
      · exact prime_oneHundredCT_479
      · exact prime_oneHundredCT_177769765424490849629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 169622221535555585008803673) ^ 84811110767777792504401836 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 169622221535555585008803673) ^ 56540740511851861669601224 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 169622221535555585008803673) ^ 2043641223319946807334984 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 169622221535555585008803673) ^ 354117372725585772460968 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (7 : ZMod 169622221535555585008803673) ^ 954168 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_679463726495874958339862989 : Nat.Prime 679463726495874958339862989 := by
  apply lucas_primality 679463726495874958339862989 (2 : ZMod 679463726495874958339862989)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (22567, 1), (6385441919, 1), (392934573113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (22567, 1), (6385441919, 1), (392934573113, 1)] : List FactorBlock).map factorBlockValue).prod) = 679463726495874958339862989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_22567
      · exact prime_oneHundredCT_6385441919
      · exact prime_oneHundredCT_392934573113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 679463726495874958339862989) ^ 339731863247937479169931494 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679463726495874958339862989) ^ 226487908831958319446620996 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679463726495874958339862989) ^ 30108730734961446286164 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679463726495874958339862989) ^ 106408254137292852 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 679463726495874958339862989) ^ 1729203213432876 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_4171314503
      · exact prime_oneHundredCT_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2273590161736196975983387693 : Nat.Prime 2273590161736196975983387693 := by
  apply lucas_primality 2273590161736196975983387693 (2 : ZMod 2273590161736196975983387693)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273590161736196975983387693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_37
      · exact prime_oneHundredCT_7389175414818054990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2273590161736196975983387693) ^ 1136795080868098487991693846 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 757863387245398991994462564 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 324798594533742425140483956 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 206690014703290634180307972 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 61448382749626945296848316 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 307692 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_2749457870006563784910143257 : Nat.Prime 2749457870006563784910143257 := by
  apply lucas_primality 2749457870006563784910143257 (5 : ZMod 2749457870006563784910143257)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (97, 1), (12844297, 1), (91950427801125241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (97, 1), (12844297, 1), (91950427801125241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749457870006563784910143257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_97
      · exact prime_oneHundredCT_12844297
      · exact prime_oneHundredCT_91950427801125241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2749457870006563784910143257) ^ 1374728935003281892455071628 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749457870006563784910143257) ^ 916485956668854594970047752 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749457870006563784910143257) ^ 28344926494913028710413848 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749457870006563784910143257) ^ 214060595921019561048 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749457870006563784910143257) ^ 29901523416 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_23645337682056448550227232011 : Nat.Prime 23645337682056448550227232011 := by
  apply lucas_primality 23645337682056448550227232011 (3 : ZMod 23645337682056448550227232011)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056448550227232011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_3
      · exact prime_oneHundredCT_5
      · exact prime_oneHundredCT_11
      · exact prime_oneHundredCT_461
      · exact prime_oneHundredCT_69997
      · exact prime_oneHundredCT_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056448550227232011) ^ 11822668841028224275113616005 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 7881779227352149516742410670 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 4729067536411289710045446402 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 2149576152914222595475202910 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 51291404950230907918063410 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 337805015672906675289330 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 10648643610 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_39408896136760747583712053357 : Nat.Prime 39408896136760747583712053357 := by
  apply lucas_primality 39408896136760747583712053357 (2 : ZMod 39408896136760747583712053357)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (971937009349, 1), (62960806628351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (971937009349, 1), (62960806628351, 1)] : List FactorBlock).map factorBlockValue).prod) = 39408896136760747583712053357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_7
      · exact prime_oneHundredCT_23
      · exact prime_oneHundredCT_971937009349
      · exact prime_oneHundredCT_62960806628351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39408896136760747583712053357) ^ 19704448068380373791856026678 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39408896136760747583712053357) ^ 5629842305251535369101721908 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39408896136760747583712053357) ^ 1713430266815684677552697972 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39408896136760747583712053357) ^ 40546759468658044 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 39408896136760747583712053357) ^ 625927434020756 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem prime_oneHundredCT_118226688410282242751136160037 : Nat.Prime 118226688410282242751136160037 := by
  apply lucas_primality 118226688410282242751136160037 (2 : ZMod 118226688410282242751136160037)
  · rw [← oneHundredCTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (2273590161736196975983387693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (2273590161736196975983387693, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredCT_2
      · exact prime_oneHundredCT_13
      · exact prime_oneHundredCT_2273590161736196975983387693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 118226688410282242751136160037) ^ 59113344205141121375568080018 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 118226688410282242751136160037) ^ 9094360646944787903933550772 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide
    · change (2 : ZMod 118226688410282242751136160037) ^ 52 ≠ 1
      rw [← oneHundredCTFastPow_eq_pow]
      decide

private theorem phi_oneHundredCT_118226688410282242751136160000 : Nat.totient 118226688410282242751136160000 = 47290399383401874189158400000 := by
  rw [← show ((([(2, 8), (5, 4), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_171401, prime_oneHundredCT_714027719, prime_oneHundredCT_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160001 : Nat.totient 118226688410282242751136160001 = 117543295672560990539249338368 := by
  rw [← show ((([(173, 1), (115829437, 1), (258169969, 1), (22853080729, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_173, prime_oneHundredCT_115829437, prime_oneHundredCT_258169969, prime_oneHundredCT_22853080729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160002 : Nat.totient 118226688410282242751136160002 = 36701951442129960421785357024 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (59, 1), (276887636227, 1), (21160885802867, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_19, prime_oneHundredCT_59, prime_oneHundredCT_276887636227, prime_oneHundredCT_21160885802867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160003 : Nat.totient 118226688410282242751136160003 = 114276378662599788547901110080 := by
  rw [← show ((([(71, 1), (73, 1), (167, 1), (136589666598058649536123, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_71, prime_oneHundredCT_73, prime_oneHundredCT_167, prime_oneHundredCT_136589666598058649536123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160004 : Nat.totient 118226688410282242751136160004 = 59113318351244137588060128000 := by
  rw [← show ((([(2, 2), (4674151, 1), (6380281, 1), (22998923, 1), (43092877, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_4674151, prime_oneHundredCT_6380281, prime_oneHundredCT_22998923, prime_oneHundredCT_43092877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160005 : Nat.totient 118226688410282242751136160005 = 52727561344961904891540750336 := by
  rw [← show ((([(3, 1), (5, 1), (7, 2), (47, 1), (313, 1), (55413389, 1), (197320078064177, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_7, prime_oneHundredCT_47, prime_oneHundredCT_313, prime_oneHundredCT_55413389, prime_oneHundredCT_197320078064177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160006 : Nat.totient 118226688410282242751136160006 = 53508762562911140449286077440 := by
  rw [← show ((([(2, 1), (11, 1), (233, 1), (1279484057, 1), (18026111139253033, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_11, prime_oneHundredCT_233, prime_oneHundredCT_1279484057, prime_oneHundredCT_18026111139253033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160007 : Nat.totient 118226688410282242751136160007 = 118226241599089502427997467600 := by
  rw [← show ((([(264601, 1), (446811192740323138427807, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_264601, prime_oneHundredCT_446811192740323138427807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160008 : Nat.totient 118226688410282242751136160008 = 38095578243210111019394826240 := by
  rw [← show ((([(2, 3), (3, 1), (43, 1), (97, 1), (12844297, 1), (91950427801125241, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_43, prime_oneHundredCT_97, prime_oneHundredCT_12844297, prime_oneHundredCT_91950427801125241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160009 : Nat.totient 118226688410282242751136160009 = 115862817997331116599160728000 := by
  rw [← show ((([(53, 1), (907, 1), (21911, 1), (372274039, 1), (301513955551, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_53, prime_oneHundredCT_907, prime_oneHundredCT_21911, prime_oneHundredCT_372274039, prime_oneHundredCT_301513955551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160010 : Nat.totient 118226688410282242751136160010 = 43652931105334981938881043648 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_13, prime_oneHundredCT_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160011 : Nat.totient 118226688410282242751136160011 = 78804787951022413132683374400 := by
  rw [← show ((([(3, 4), (11093, 1), (14887, 1), (130211, 1), (67877623794931, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_11093, prime_oneHundredCT_14887, prime_oneHundredCT_130211, prime_oneHundredCT_67877623794931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160012 : Nat.totient 118226688410282242751136160012 = 50618561308710241179351344832 := by
  rw [← show ((([(2, 2), (7, 1), (1013, 1), (46174027, 1), (90271424483937779, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_7, prime_oneHundredCT_1013, prime_oneHundredCT_46174027, prime_oneHundredCT_90271424483937779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160013 : Nat.totient 118226688410282242751136160013 = 111254684452410562733898708480 := by
  rw [← show ((([(17, 1), (6361, 1), (1093304682118814492274949, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_17, prime_oneHundredCT_6361, prime_oneHundredCT_1093304682118814492274949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160014 : Nat.totient 118226688410282242751136160014 = 39392358622645447228032773688 := by
  rw [← show ((([(2, 1), (3, 1), (2383, 1), (8268757057650177839637443, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_2383, prime_oneHundredCT_8268757057650177839637443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160015 : Nat.totient 118226688410282242751136160015 = 94581350728013731875911310912 := by
  rw [← show ((([(5, 1), (446011079209, 1), (53015135238325067, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_446011079209, prime_oneHundredCT_53015135238325067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160016 : Nat.totient 118226688410282242751136160016 = 58725076372807273625823105024 := by
  rw [← show ((([(2, 4), (157, 1), (4999, 1), (87683238689, 1), (107373267763, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_157, prime_oneHundredCT_4999, prime_oneHundredCT_87683238689, prime_oneHundredCT_107373267763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160017 : Nat.totient 118226688410282242751136160017 = 71641462137626587043507947200 := by
  rw [← show ((([(3, 1), (11, 1), (6469, 1), (553814642374973616601021, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_11, prime_oneHundredCT_6469, prime_oneHundredCT_553814642374973616601021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160018 : Nat.totient 118226688410282242751136160018 = 59112644166722245434147444804 := by
  rw [← show ((([(2, 1), (84443, 1), (700038418875941420550763, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_84443, prime_oneHundredCT_700038418875941420550763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160019 : Nat.totient 118226688410282242751136160019 = 101337161493974351300195563080 := by
  rw [← show ((([(7, 1), (183155697031, 1), (92214040783541507, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_7, prime_oneHundredCT_183155697031, prime_oneHundredCT_92214040783541507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160020 : Nat.totient 118226688410282242751136160020 = 31527064988390916613153988352 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_607213, prime_oneHundredCT_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160021 : Nat.totient 118226688410282242751136160021 = 108870144611528086390144873728 := by
  rw [← show ((([(19, 1), (37, 1), (1019, 1), (165038784307659787998353, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_19, prime_oneHundredCT_37, prime_oneHundredCT_1019, prime_oneHundredCT_165038784307659787998353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160022 : Nat.totient 118226688410282242751136160022 = 56543196646665156054315124392 := by
  rw [← show ((([(2, 1), (23, 1), (26198603, 1), (98102383559288524519, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_23, prime_oneHundredCT_26198603, prime_oneHundredCT_98102383559288524519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160023 : Nat.totient 118226688410282242751136160023 = 72685660736761387624207231200 := by
  rw [← show ((([(3, 1), (13, 1), (1051, 1), (2884351616538150302547907, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_13, prime_oneHundredCT_1051, prime_oneHundredCT_2884351616538150302547907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160024 : Nat.totient 118226688410282242751136160024 = 59109728488805247745218285312 := by
  rw [← show ((([(2, 3), (16349, 1), (659795388823, 1), (1370014198489, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_16349, prime_oneHundredCT_659795388823, prime_oneHundredCT_1370014198489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160025 : Nat.totient 118226688410282242751136160025 = 94568841583050739932652060800 := by
  rw [← show ((([(5, 2), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_7561, prime_oneHundredCT_2416168199, prime_oneHundredCT_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160026 : Nat.totient 118226688410282242751136160026 = 33779027027147241521571128640 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1260341, 1), (12748193219, 1), (175198156807, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_7, prime_oneHundredCT_1260341, prime_oneHundredCT_12748193219, prime_oneHundredCT_175198156807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160027 : Nat.totient 118226688410282242751136160027 = 118226665876804918894795956336 := by
  rw [← show ((([(5246713, 1), (22533477323856334956979, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5246713, prime_oneHundredCT_22533477323856334956979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160028 : Nat.totient 118226688410282242751136160028 = 51885028652744704298002968000 := by
  rw [← show ((([(2, 2), (11, 1), (29, 1), (40151, 1), (2307642263509371299503, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_11, prime_oneHundredCT_29, prime_oneHundredCT_40151, prime_oneHundredCT_2307642263509371299503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160029 : Nat.totient 118226688410282242751136160029 = 75586877376426578268185587200 := by
  rw [← show ((([(3, 2), (31, 1), (113, 1), (5683, 1), (755239, 1), (873717055755871, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_31, prime_oneHundredCT_113, prime_oneHundredCT_5683, prime_oneHundredCT_755239, prime_oneHundredCT_873717055755871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160030 : Nat.totient 118226688410282242751136160030 = 44423441234320550753494241280 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_17, prime_oneHundredCT_521, prime_oneHundredCT_23096547757, prime_oneHundredCT_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160031 : Nat.totient 118226688410282242751136160031 = 116462110928114272129476327000 := by
  rw [← show ((([(67, 1), (2695349743, 1), (654674757345372251, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_67, prime_oneHundredCT_2695349743, prime_oneHundredCT_654674757345372251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160032 : Nat.totient 118226688410282242751136160032 = 39408270497107366441535539200 := by
  rw [← show ((([(2, 5), (3, 1), (63907, 1), (6496339, 1), (14483401, 1), (204812579, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_63907, prime_oneHundredCT_6496339, prime_oneHundredCT_14483401, prime_oneHundredCT_204812579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160033 : Nat.totient 118226688410282242751136160033 = 101219187965694799125489057792 := by
  rw [← show ((([(7, 1), (929, 1), (14437, 1), (56503, 1), (1144993, 1), (19464823757, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_7, prime_oneHundredCT_929, prime_oneHundredCT_14437, prime_oneHundredCT_56503, prime_oneHundredCT_1144993, prime_oneHundredCT_19464823757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160034 : Nat.totient 118226688410282242751136160034 = 59113305417035682790887236580 := by
  rw [← show ((([(2, 1), (1524007, 1), (38788105438584679319431, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_1524007, prime_oneHundredCT_38788105438584679319431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160035 : Nat.totient 118226688410282242751136160035 = 63054228255217002438515602400 := by
  rw [← show ((([(3, 1), (5, 1), (11333351, 1), (695450024211916627019, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_11333351, prime_oneHundredCT_695450024211916627019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160036 : Nat.totient 118226688410282242751136160036 = 54566163881668727423601304608 := by
  rw [← show ((([(2, 2), (13, 1), (2273590161736196975983387693, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_13, prime_oneHundredCT_2273590161736196975983387693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160037 : Nat.totient 118226688410282242751136160037 = 118226688410282242751136160036 := by
  rw [← show ((([(118226688410282242751136160037, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_118226688410282242751136160037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160038 : Nat.totient 118226688410282242751136160038 = 39283439150771356063876404480 := by
  rw [← show ((([(2, 1), (3, 3), (457, 1), (1039, 1), (28541, 1), (161555159326910779, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_457, prime_oneHundredCT_1039, prime_oneHundredCT_28541, prime_oneHundredCT_161555159326910779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160039 : Nat.totient 118226688410282242751136160039 = 107477570170170695169376112160 := by
  rw [← show ((([(11, 1), (89399, 1), (3050023, 1), (39417317410818037, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_11, prime_oneHundredCT_89399, prime_oneHundredCT_3050023, prime_oneHundredCT_39417317410818037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160040 : Nat.totient 118226688410282242751136160040 = 37370457330634725440398295040 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_7, prime_oneHundredCT_19, prime_oneHundredCT_41, prime_oneHundredCT_397, prime_oneHundredCT_13617913, prime_oneHundredCT_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160041 : Nat.totient 118226688410282242751136160041 = 78816154365076668137745337440 := by
  rw [← show ((([(3, 1), (48121, 1), (818954222413514839336507, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_48121, prime_oneHundredCT_818954222413514839336507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160042 : Nat.totient 118226688410282242751136160042 = 58754183343010616933087896368 := by
  rw [← show ((([(2, 1), (199, 1), (947, 1), (67997183, 1), (4613086018624079, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_199, prime_oneHundredCT_947, prime_oneHundredCT_67997183, prime_oneHundredCT_4613086018624079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160043 : Nat.totient 118226688410282242751136160043 = 118206821870074430806182912000 := by
  rw [← show ((([(5953, 1), (18124331, 1), (1095765587763403201, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5953, prime_oneHundredCT_18124331, prime_oneHundredCT_1095765587763403201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160044 : Nat.totient 118226688410282242751136160044 = 39408843108870691350843269184 := by
  rw [← show ((([(2, 2), (3, 1), (743173, 1), (13256972514058216452869, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_743173, prime_oneHundredCT_13256972514058216452869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160045 : Nat.totient 118226688410282242751136160045 = 90070153523037250058979712768 := by
  rw [← show ((([(5, 1), (23, 1), (227, 1), (235397, 1), (2276699, 1), (8450556055043, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_23, prime_oneHundredCT_227, prime_oneHundredCT_235397, prime_oneHundredCT_2276699, prime_oneHundredCT_8450556055043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160046 : Nat.totient 118226688410282242751136160046 = 59099191436550328377155130240 := by
  rw [← show ((([(2, 1), (4177, 1), (89111779, 1), (158812959932849581, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_4177, prime_oneHundredCT_89111779, prime_oneHundredCT_158812959932849581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160047 : Nat.totient 118226688410282242751136160047 = 63584101329899693580442976256 := by
  rw [← show ((([(3, 2), (7, 1), (17, 1), (110389064808853634688269057, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_7, prime_oneHundredCT_17, prime_oneHundredCT_110389064808853634688269057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160048 : Nat.totient 118226688410282242751136160048 = 57409197342493262598097931520 := by
  rw [← show ((([(2, 4), (61, 1), (83, 1), (1663, 1), (877597476325376642987, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_61, prime_oneHundredCT_83, prime_oneHundredCT_1663, prime_oneHundredCT_877597476325376642987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160049 : Nat.totient 118226688410282242751136160049 = 109131181306973267713387900560 := by
  rw [← show ((([(13, 1), (95191, 1), (95538030348927817797203, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_13, prime_oneHundredCT_95191, prime_oneHundredCT_95538030348927817797203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160050 : Nat.totient 118226688410282242751136160050 = 28598435399825824731836160000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_11, prime_oneHundredCT_461, prime_oneHundredCT_69997, prime_oneHundredCT_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160051 : Nat.totient 118226688410282242751136160051 = 115477230540275678966226016752 := by
  rw [← show ((([(43, 1), (2749457870006563784910143257, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_43, prime_oneHundredCT_2749457870006563784910143257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160052 : Nat.totient 118226688410282242751136160052 = 57855530902346824085692921584 := by
  rw [← show ((([(2, 2), (47, 2), (700643, 1), (19096906877256609199, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_47, prime_oneHundredCT_700643, prime_oneHundredCT_19096906877256609199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160053 : Nat.totient 118226688410282242751136160053 = 78807423159165713441768515008 := by
  rw [← show ((([(3, 1), (7603, 1), (39602887, 1), (270151933, 1), (484478327, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_7603, prime_oneHundredCT_39602887, prime_oneHundredCT_270151933, prime_oneHundredCT_484478327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160054 : Nat.totient 118226688410282242751136160054 = 50565383992777033078441701840 := by
  rw [← show ((([(2, 1), (7, 2), (491, 1), (24205387, 1), (101506984564892419, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_7, prime_oneHundredCT_491, prime_oneHundredCT_24205387, prime_oneHundredCT_101506984564892419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160055 : Nat.totient 118226688410282242751136160055 = 94581350728225794200908928040 := by
  rw [← show ((([(5, 1), (23645337682056448550227232011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_23645337682056448550227232011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160056 : Nat.totient 118226688410282242751136160056 = 38993570165391703975462212864 := by
  rw [← show ((([(2, 3), (3, 2), (109, 1), (727, 1), (588827, 1), (35191226542465943, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_109, prime_oneHundredCT_727, prime_oneHundredCT_588827, prime_oneHundredCT_35191226542465943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160057 : Nat.totient 118226688410282242751136160057 = 112861474718804451862762315776 := by
  rw [← show ((([(29, 1), (89, 1), (19319, 1), (19384979, 1), (122314386981697, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_29, prime_oneHundredCT_89, prime_oneHundredCT_19319, prime_oneHundredCT_19384979, prime_oneHundredCT_122314386981697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160058 : Nat.totient 118226688410282242751136160058 = 57495582902985441272929316160 := by
  rw [← show ((([(2, 1), (37, 1), (2861, 1), (558426407371653470016797, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_37, prime_oneHundredCT_2861, prime_oneHundredCT_558426407371653470016797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160059 : Nat.totient 118226688410282242751136160059 = 74669448018420500898294244512 := by
  rw [← show ((([(3, 1), (19, 1), (1896883, 1), (2187018947, 1), (499974182987, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_19, prime_oneHundredCT_1896883, prime_oneHundredCT_2187018947, prime_oneHundredCT_499974182987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160060 : Nat.totient 118226688410282242751136160060 = 45765156991158443238976235520 := by
  rw [← show ((([(2, 2), (5, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_31, prime_oneHundredCT_3599009, prime_oneHundredCT_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160061 : Nat.totient 118226688410282242751136160061 = 90560387861576623104407098560 := by
  rw [← show ((([(7, 1), (11, 1), (59, 1), (31567, 1), (4177664207, 1), (197335830883, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_7, prime_oneHundredCT_11, prime_oneHundredCT_59, prime_oneHundredCT_31567, prime_oneHundredCT_4177664207, prime_oneHundredCT_197335830883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160062 : Nat.totient 118226688410282242751136160062 = 35691075744392769145675820928 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (53, 1), (16937230103, 1), (129885093883087, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_13, prime_oneHundredCT_53, prime_oneHundredCT_16937230103, prime_oneHundredCT_129885093883087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160063 : Nat.totient 118226688410282242751136160063 = 118225973889885475605352640400 := by
  rw [← show ((([(165463, 1), (714520396767145783354201, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_165463, prime_oneHundredCT_714520396767145783354201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160064 : Nat.totient 118226688410282242751136160064 = 55343393444353008804754022400 := by
  rw [← show ((([(2, 6), (17, 1), (191, 1), (39341, 1), (14461317705429316663, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_17, prime_oneHundredCT_191, prime_oneHundredCT_39341, prime_oneHundredCT_14461317705429316663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160065 : Nat.totient 118226688410282242751136160065 = 62991612677647488615404682240 := by
  rw [← show ((([(3, 3), (5, 1), (1223, 1), (8849, 1), (15971, 1), (5066744382093707, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_1223, prime_oneHundredCT_8849, prime_oneHundredCT_15971, prime_oneHundredCT_5066744382093707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160066 : Nat.totient 118226688410282242751136160066 = 59113344205140635044434072768 := by
  rw [← show ((([(2, 1), (239147013649849, 1), (247184120357417, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_239147013649849, prime_oneHundredCT_247184120357417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160067 : Nat.totient 118226688410282242751136160067 = 118030394102619726758195136000 := by
  rw [← show ((([(619, 1), (22381, 1), (4893853, 1), (1743791147825201, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_619, prime_oneHundredCT_22381, prime_oneHundredCT_4893853, prime_oneHundredCT_1743791147825201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160068 : Nat.totient 118226688410282242751136160068 = 32310399317062011716638742400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (23, 1), (971937009349, 1), (62960806628351, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_7, prime_oneHundredCT_23, prime_oneHundredCT_971937009349, prime_oneHundredCT_62960806628351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160069 : Nat.totient 118226688410282242751136160069 = 118212835626185003812146183072 := by
  rw [← show ((([(8719, 1), (403289, 1), (33622691112624143459, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_8719, prime_oneHundredCT_403289, prime_oneHundredCT_33622691112624143459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160070 : Nat.totient 118226688410282242751136160070 = 47263228657575396869984083104 := by
  rw [← show ((([(2, 1), (5, 1), (1723, 1), (6861676634375057617593509, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_1723, prime_oneHundredCT_6861676634375057617593509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160071 : Nat.totient 118226688410282242751136160071 = 78817792273521495167424106712 := by
  rw [← show ((([(3, 1), (39408896136760747583712053357, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_39408896136760747583712053357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160072 : Nat.totient 118226688410282242751136160072 = 53427508417542588102918144000 := by
  rw [← show ((([(2, 3), (11, 2), (197, 1), (2341, 1), (4889, 1), (11069, 1), (105277, 1), (46484761, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_11, prime_oneHundredCT_197, prime_oneHundredCT_2341, prime_oneHundredCT_4889, prime_oneHundredCT_11069, prime_oneHundredCT_105277, prime_oneHundredCT_46484761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160073 : Nat.totient 118226688410282242751136160073 = 118226448463409210302595128800 := by
  rw [← show ((([(492871, 1), (1611172153, 1), (148881354880871, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_492871, prime_oneHundredCT_1611172153, prime_oneHundredCT_148881354880871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160074 : Nat.totient 118226688410282242751136160074 = 38715568537562122914699264000 := by
  rw [← show ((([(2, 1), (3, 2), (71, 1), (311, 1), (3413, 1), (19489, 1), (5863469, 1), (762682541, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_71, prime_oneHundredCT_311, prime_oneHundredCT_3413, prime_oneHundredCT_19489, prime_oneHundredCT_5863469, prime_oneHundredCT_762682541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160075 : Nat.totient 118226688410282242751136160075 = 73282438205198433349447680000 := by
  rw [← show ((([(5, 2), (7, 1), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_7, prime_oneHundredCT_13, prime_oneHundredCT_101, prime_oneHundredCT_103, prime_oneHundredCT_1163, prime_oneHundredCT_3221, prime_oneHundredCT_20357, prime_oneHundredCT_53279, prime_oneHundredCT_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160076 : Nat.totient 118226688410282242751136160076 = 58301594163872379735994414080 := by
  rw [← show ((([(2, 2), (73, 1), (29473, 1), (13737519737159276350811, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_73, prime_oneHundredCT_29473, prime_oneHundredCT_13737519737159276350811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160077 : Nat.totient 118226688410282242751136160077 = 78817357625017818708850142592 := by
  rw [← show ((([(3, 1), (181459, 1), (269391113, 1), (806180877316877, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_181459, prime_oneHundredCT_269391113, prime_oneHundredCT_806180877316877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160078 : Nat.totient 118226688410282242751136160078 = 55293228023996092212723214080 := by
  rw [← show ((([(2, 1), (19, 2), (79, 1), (2072770581196434705830081, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_19, prime_oneHundredCT_79, prime_oneHundredCT_2072770581196434705830081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160079 : Nat.totient 118226688410282242751136160079 = 118059936978010412135716557696 := by
  rw [← show ((([(709, 1), (1086077747, 1), (153535346828908273, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_709, prime_oneHundredCT_1086077747, prime_oneHundredCT_153535346828908273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160080 : Nat.totient 118226688410282242751136160080 = 31520860083611012264792463360 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_5879, prime_oneHundredCT_35267, prime_oneHundredCT_88812211, prime_oneHundredCT_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160081 : Nat.totient 118226688410282242751136160081 = 108558221782755574405634350080 := by
  rw [← show ((([(17, 1), (41, 1), (169622221535555585008803673, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_17, prime_oneHundredCT_41, prime_oneHundredCT_169622221535555585008803673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160082 : Nat.totient 118226688410282242751136160082 = 50668568060736789838170949248 := by
  rw [← show ((([(2, 1), (7, 1), (3993889, 1), (2114421171413953430767, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_7, prime_oneHundredCT_3993889, prime_oneHundredCT_2114421171413953430767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160083 : Nat.totient 118226688410282242751136160083 = 71643892051998103157988044400 := by
  rw [← show ((([(3, 2), (11, 1), (8287, 1), (144106307933055964192591, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_11, prime_oneHundredCT_8287, prime_oneHundredCT_144106307933055964192591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160084 : Nat.totient 118226688410282242751136160084 = 58728827565592671117319718400 := by
  rw [← show ((([(2, 2), (181, 1), (1031, 1), (65437, 1), (8487079, 1), (285191559557, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_181, prime_oneHundredCT_1031, prime_oneHundredCT_65437, prime_oneHundredCT_8487079, prime_oneHundredCT_285191559557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160085 : Nat.totient 118226688410282242751136160085 = 93662040409819074588205270080 := by
  rw [← show ((([(5, 1), (107, 1), (3187, 1), (15683, 1), (4421305627276911211, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_5, prime_oneHundredCT_107, prime_oneHundredCT_3187, prime_oneHundredCT_15683, prime_oneHundredCT_4421305627276911211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160086 : Nat.totient 118226688410282242751136160086 = 38049968683768997667032327328 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (679463726495874958339862989, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_29, prime_oneHundredCT_679463726495874958339862989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160087 : Nat.totient 118226688410282242751136160087 = 118226688410213510024532829600 := by
  rw [← show ((([(1720136143601, 1), (68731006467186887, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_1720136143601, prime_oneHundredCT_68731006467186887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160088 : Nat.totient 118226688410282242751136160088 = 54516497546212721560912896000 := by
  rw [← show ((([(2, 3), (13, 1), (1151, 1), (24137, 1), (40918864317638395681, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_13, prime_oneHundredCT_1151, prime_oneHundredCT_24137, prime_oneHundredCT_40918864317638395681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160089 : Nat.totient 118226688410282242751136160089 = 67493705272491238133291936640 := by
  rw [← show ((([(3, 1), (7, 1), (1049, 1), (5366865877265524660726141, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_7, prime_oneHundredCT_1049, prime_oneHundredCT_5366865877265524660726141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160090 : Nat.totient 118226688410282242751136160090 = 46869976438413716434016278080 := by
  rw [← show ((([(2, 1), (5, 1), (127, 1), (971, 1), (3962759, 1), (24193288987440403, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_127, prime_oneHundredCT_971, prime_oneHundredCT_3962759, prime_oneHundredCT_24193288987440403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160091 : Nat.totient 118226688410282242751136160091 = 109409132810910482309030325120 := by
  rw [← show ((([(23, 1), (31, 1), (3733, 1), (208799549117, 1), (212734755587, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_23, prime_oneHundredCT_31, prime_oneHundredCT_3733, prime_oneHundredCT_208799549117, prime_oneHundredCT_212734755587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160092 : Nat.totient 118226688410282242751136160092 = 39226387319400446684748003744 := by
  rw [← show ((([(2, 2), (3, 4), (223, 1), (6779, 1), (241379296820428958299, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_223, prime_oneHundredCT_6779, prime_oneHundredCT_241379296820428958299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160093 : Nat.totient 118226688410282242751136160093 = 118224949420595352266681279040 := by
  rw [← show ((([(69557, 1), (3009781, 1), (564728604530869829, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_69557, prime_oneHundredCT_3009781, prime_oneHundredCT_564728604530869829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160094 : Nat.totient 118226688410282242751136160094 = 52473806704908082311572926080 := by
  rw [← show ((([(2, 1), (11, 1), (43, 1), (3313, 1), (37722715885170866626103, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_11, prime_oneHundredCT_43, prime_oneHundredCT_3313, prime_oneHundredCT_37722715885170866626103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160095 : Nat.totient 118226688410282242751136160095 = 61349792940246162717992068992 := by
  rw [← show ((([(3, 1), (5, 1), (37, 1), (225223, 1), (945822852012035820923, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_5, prime_oneHundredCT_37, prime_oneHundredCT_225223, prime_oneHundredCT_945822852012035820923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160096 : Nat.totient 118226688410282242751136160096 = 50623701578016950912310706176 := by
  rw [← show ((([(2, 5), (7, 1), (1129, 1), (43064212757, 1), (10855680484993, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_7, prime_oneHundredCT_1129, prime_oneHundredCT_43064212757, prime_oneHundredCT_10855680484993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160097 : Nat.totient 118226688410282242751136160097 = 111989649139965446096773601280 := by
  rw [← show ((([(19, 1), (7681, 1), (810110309172203747806523, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_19, prime_oneHundredCT_7681, prime_oneHundredCT_810110309172203747806523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160098 : Nat.totient 118226688410282242751136160098 = 36130186338637536476551249920 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (67, 1), (137, 1), (277, 1), (3881, 1), (117461778302995013, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_3, prime_oneHundredCT_17, prime_oneHundredCT_67, prime_oneHundredCT_137, prime_oneHundredCT_277, prime_oneHundredCT_3881, prime_oneHundredCT_117461778302995013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160099 : Nat.totient 118226688410282242751136160099 = 115682817618394029463361631936 := by
  rw [← show ((([(47, 1), (4073, 1), (617594268484635418250629, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_47, prime_oneHundredCT_4073, prime_oneHundredCT_617594268484635418250629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160100 : Nat.totient 118226688410282242751136160100 = 47290675364109023454609456000 := by
  rw [← show ((([(2, 2), (5, 2), (14328271708661, 1), (82512874416541, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_2, prime_oneHundredCT_5, prime_oneHundredCT_14328271708661, prime_oneHundredCT_82512874416541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredCT_118226688410282242751136160101 : Nat.totient 118226688410282242751136160101 = 72753674269225803883841100960 := by
  rw [← show ((([(3, 2), (13, 1), (60083, 1), (16818143506935383652491, 1)] : List FactorBlock).map factorBlockValue).prod) = 118226688410282242751136160101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredCT_3, prime_oneHundredCT_13, prime_oneHundredCT_60083, prime_oneHundredCT_16818143506935383652491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredCT : certifiedKill 1 118226688410282242751136159999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredCT_118226688410282242751136160000, phi_oneHundredCT_118226688410282242751136160001, phi_oneHundredCT_118226688410282242751136160002,
    phi_oneHundredCT_118226688410282242751136160003, phi_oneHundredCT_118226688410282242751136160004, phi_oneHundredCT_118226688410282242751136160005,
    phi_oneHundredCT_118226688410282242751136160006, phi_oneHundredCT_118226688410282242751136160007, phi_oneHundredCT_118226688410282242751136160008,
    phi_oneHundredCT_118226688410282242751136160009, phi_oneHundredCT_118226688410282242751136160010, phi_oneHundredCT_118226688410282242751136160011,
    phi_oneHundredCT_118226688410282242751136160012, phi_oneHundredCT_118226688410282242751136160013, phi_oneHundredCT_118226688410282242751136160014,
    phi_oneHundredCT_118226688410282242751136160015, phi_oneHundredCT_118226688410282242751136160016, phi_oneHundredCT_118226688410282242751136160017,
    phi_oneHundredCT_118226688410282242751136160018, phi_oneHundredCT_118226688410282242751136160019, phi_oneHundredCT_118226688410282242751136160020,
    phi_oneHundredCT_118226688410282242751136160021, phi_oneHundredCT_118226688410282242751136160022, phi_oneHundredCT_118226688410282242751136160023,
    phi_oneHundredCT_118226688410282242751136160024, phi_oneHundredCT_118226688410282242751136160025, phi_oneHundredCT_118226688410282242751136160026,
    phi_oneHundredCT_118226688410282242751136160027, phi_oneHundredCT_118226688410282242751136160028, phi_oneHundredCT_118226688410282242751136160029,
    phi_oneHundredCT_118226688410282242751136160030, phi_oneHundredCT_118226688410282242751136160031, phi_oneHundredCT_118226688410282242751136160032,
    phi_oneHundredCT_118226688410282242751136160033, phi_oneHundredCT_118226688410282242751136160034, phi_oneHundredCT_118226688410282242751136160035,
    phi_oneHundredCT_118226688410282242751136160036, phi_oneHundredCT_118226688410282242751136160037, phi_oneHundredCT_118226688410282242751136160038,
    phi_oneHundredCT_118226688410282242751136160039, phi_oneHundredCT_118226688410282242751136160040, phi_oneHundredCT_118226688410282242751136160041,
    phi_oneHundredCT_118226688410282242751136160042, phi_oneHundredCT_118226688410282242751136160043, phi_oneHundredCT_118226688410282242751136160044,
    phi_oneHundredCT_118226688410282242751136160045, phi_oneHundredCT_118226688410282242751136160046, phi_oneHundredCT_118226688410282242751136160047,
    phi_oneHundredCT_118226688410282242751136160048, phi_oneHundredCT_118226688410282242751136160049, phi_oneHundredCT_118226688410282242751136160050,
    phi_oneHundredCT_118226688410282242751136160051, phi_oneHundredCT_118226688410282242751136160052, phi_oneHundredCT_118226688410282242751136160053,
    phi_oneHundredCT_118226688410282242751136160054, phi_oneHundredCT_118226688410282242751136160055, phi_oneHundredCT_118226688410282242751136160056,
    phi_oneHundredCT_118226688410282242751136160057, phi_oneHundredCT_118226688410282242751136160058, phi_oneHundredCT_118226688410282242751136160059,
    phi_oneHundredCT_118226688410282242751136160060, phi_oneHundredCT_118226688410282242751136160061, phi_oneHundredCT_118226688410282242751136160062,
    phi_oneHundredCT_118226688410282242751136160063, phi_oneHundredCT_118226688410282242751136160064, phi_oneHundredCT_118226688410282242751136160065,
    phi_oneHundredCT_118226688410282242751136160066, phi_oneHundredCT_118226688410282242751136160067, phi_oneHundredCT_118226688410282242751136160068,
    phi_oneHundredCT_118226688410282242751136160069, phi_oneHundredCT_118226688410282242751136160070, phi_oneHundredCT_118226688410282242751136160071,
    phi_oneHundredCT_118226688410282242751136160072, phi_oneHundredCT_118226688410282242751136160073, phi_oneHundredCT_118226688410282242751136160074,
    phi_oneHundredCT_118226688410282242751136160075, phi_oneHundredCT_118226688410282242751136160076, phi_oneHundredCT_118226688410282242751136160077,
    phi_oneHundredCT_118226688410282242751136160078, phi_oneHundredCT_118226688410282242751136160079, phi_oneHundredCT_118226688410282242751136160080,
    phi_oneHundredCT_118226688410282242751136160081, phi_oneHundredCT_118226688410282242751136160082, phi_oneHundredCT_118226688410282242751136160083,
    phi_oneHundredCT_118226688410282242751136160084, phi_oneHundredCT_118226688410282242751136160085, phi_oneHundredCT_118226688410282242751136160086,
    phi_oneHundredCT_118226688410282242751136160087, phi_oneHundredCT_118226688410282242751136160088, phi_oneHundredCT_118226688410282242751136160089,
    phi_oneHundredCT_118226688410282242751136160090, phi_oneHundredCT_118226688410282242751136160091, phi_oneHundredCT_118226688410282242751136160092,
    phi_oneHundredCT_118226688410282242751136160093, phi_oneHundredCT_118226688410282242751136160094, phi_oneHundredCT_118226688410282242751136160095,
    phi_oneHundredCT_118226688410282242751136160096, phi_oneHundredCT_118226688410282242751136160097, phi_oneHundredCT_118226688410282242751136160098,
    phi_oneHundredCT_118226688410282242751136160099, phi_oneHundredCT_118226688410282242751136160100, phi_oneHundredCT_118226688410282242751136160101
    ]

end TotientTailPeriodKiller
end Erdos249257
