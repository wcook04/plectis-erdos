import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwelveDFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwelveDFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwelveDFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwelveDFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwelveDFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwelveDFFastPow a n * oneHundredTwelveDFFastPow a n * a else oneHundredTwelveDFFastPow a n * oneHundredTwelveDFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwelveDF_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwelveDF_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwelveDF_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwelveDF_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwelveDF_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwelveDF_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwelveDF_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwelveDF_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwelveDF_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwelveDF_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwelveDF_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwelveDF_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwelveDF_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwelveDF_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwelveDF_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwelveDF_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwelveDF_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwelveDF_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwelveDF_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwelveDF_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwelveDF_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwelveDF_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwelveDF_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwelveDF_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwelveDF_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwelveDF_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwelveDF_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwelveDF_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwelveDF_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwelveDF_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwelveDF_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwelveDF_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwelveDF_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwelveDF_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwelveDF_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwelveDF_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwelveDF_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwelveDF_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwelveDF_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwelveDF_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwelveDF_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwelveDF_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwelveDF_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwelveDF_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwelveDF_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwelveDF_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwelveDF_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwelveDF_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwelveDF_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwelveDF_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwelveDF_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwelveDF_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwelveDF_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwelveDF_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwelveDF_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwelveDF_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwelveDF_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwelveDF_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwelveDF_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwelveDF_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwelveDF_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwelveDF_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwelveDF_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwelveDF_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwelveDF_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwelveDF_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwelveDF_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwelveDF_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwelveDF_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwelveDF_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwelveDF_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwelveDF_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwelveDF_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwelveDF_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTwelveDF_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTwelveDF_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwelveDF_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwelveDF_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredTwelveDF_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwelveDF_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwelveDF_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwelveDF_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredTwelveDF_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwelveDF_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwelveDF_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwelveDF_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredTwelveDF_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredTwelveDF_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwelveDF_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwelveDF_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwelveDF_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredTwelveDF_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredTwelveDF_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwelveDF_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredTwelveDF_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTwelveDF_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredTwelveDF_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwelveDF_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwelveDF_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredTwelveDF_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredTwelveDF_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredTwelveDF_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTwelveDF_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwelveDF_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredTwelveDF_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredTwelveDF_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredTwelveDF_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwelveDF_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwelveDF_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredTwelveDF_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwelveDF_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwelveDF_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredTwelveDF_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredTwelveDF_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwelveDF_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredTwelveDF_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwelveDF_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTwelveDF_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredTwelveDF_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwelveDF_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredTwelveDF_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredTwelveDF_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredTwelveDF_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredTwelveDF_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwelveDF_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredTwelveDF_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredTwelveDF_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredTwelveDF_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredTwelveDF_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredTwelveDF_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredTwelveDF_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredTwelveDF_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredTwelveDF_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredTwelveDF_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredTwelveDF_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredTwelveDF_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredTwelveDF_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredTwelveDF_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredTwelveDF_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredTwelveDF_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwelveDF_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredTwelveDF_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredTwelveDF_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredTwelveDF_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredTwelveDF_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredTwelveDF_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredTwelveDF_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredTwelveDF_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredTwelveDF_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_oneHundredTwelveDF_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredTwelveDF_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredTwelveDF_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredTwelveDF_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredTwelveDF_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredTwelveDF_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredTwelveDF_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_oneHundredTwelveDF_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_oneHundredTwelveDF_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredTwelveDF_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredTwelveDF_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredTwelveDF_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredTwelveDF_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredTwelveDF_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwelveDF_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredTwelveDF_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredTwelveDF_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredTwelveDF_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredTwelveDF_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredTwelveDF_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredTwelveDF_4079 : Nat.Prime 4079 := by norm_num

private theorem prime_oneHundredTwelveDF_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredTwelveDF_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredTwelveDF_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredTwelveDF_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredTwelveDF_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_oneHundredTwelveDF_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_oneHundredTwelveDF_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_oneHundredTwelveDF_5507 : Nat.Prime 5507 := by norm_num

private theorem prime_oneHundredTwelveDF_5639 : Nat.Prime 5639 := by norm_num

private theorem prime_oneHundredTwelveDF_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredTwelveDF_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredTwelveDF_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_oneHundredTwelveDF_5857 : Nat.Prime 5857 := by norm_num

private theorem prime_oneHundredTwelveDF_6571 : Nat.Prime 6571 := by norm_num

private theorem prime_oneHundredTwelveDF_6577 : Nat.Prime 6577 := by norm_num

private theorem prime_oneHundredTwelveDF_6691 : Nat.Prime 6691 := by norm_num

private theorem prime_oneHundredTwelveDF_6841 : Nat.Prime 6841 := by norm_num

private theorem prime_oneHundredTwelveDF_6949 : Nat.Prime 6949 := by norm_num

private theorem prime_oneHundredTwelveDF_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_oneHundredTwelveDF_7459 : Nat.Prime 7459 := by norm_num

private theorem prime_oneHundredTwelveDF_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredTwelveDF_7853 : Nat.Prime 7853 := by norm_num

private theorem prime_oneHundredTwelveDF_8233 : Nat.Prime 8233 := by norm_num

private theorem prime_oneHundredTwelveDF_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwelveDF_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredTwelveDF_8599 : Nat.Prime 8599 := by norm_num

private theorem prime_oneHundredTwelveDF_8693 : Nat.Prime 8693 := by norm_num

private theorem prime_oneHundredTwelveDF_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredTwelveDF_10181 : Nat.Prime 10181 := by norm_num

private theorem prime_oneHundredTwelveDF_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredTwelveDF_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredTwelveDF_10993 : Nat.Prime 10993 := by norm_num

private theorem prime_oneHundredTwelveDF_11717 : Nat.Prime 11717 := by norm_num

private theorem prime_oneHundredTwelveDF_12373 : Nat.Prime 12373 := by norm_num

private theorem prime_oneHundredTwelveDF_12409 : Nat.Prime 12409 := by norm_num

private theorem prime_oneHundredTwelveDF_12413 : Nat.Prime 12413 := by norm_num

private theorem prime_oneHundredTwelveDF_12919 : Nat.Prime 12919 := by norm_num

private theorem prime_oneHundredTwelveDF_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_oneHundredTwelveDF_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_oneHundredTwelveDF_13627 : Nat.Prime 13627 := by norm_num

private theorem prime_oneHundredTwelveDF_16063 : Nat.Prime 16063 := by norm_num

private theorem prime_oneHundredTwelveDF_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredTwelveDF_16787 : Nat.Prime 16787 := by norm_num

private theorem prime_oneHundredTwelveDF_16889 : Nat.Prime 16889 := by norm_num

private theorem prime_oneHundredTwelveDF_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwelveDF_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredTwelveDF_17257 : Nat.Prime 17257 := by norm_num

private theorem prime_oneHundredTwelveDF_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredTwelveDF_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredTwelveDF_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwelveDF_21011 : Nat.Prime 21011 := by norm_num

private theorem prime_oneHundredTwelveDF_22307 : Nat.Prime 22307 := by norm_num

private theorem prime_oneHundredTwelveDF_22787 : Nat.Prime 22787 := by norm_num

private theorem prime_oneHundredTwelveDF_22907 : Nat.Prime 22907 := by norm_num

private theorem prime_oneHundredTwelveDF_24109 : Nat.Prime 24109 := by norm_num

private theorem prime_oneHundredTwelveDF_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredTwelveDF_25243 : Nat.Prime 25243 := by norm_num

private theorem prime_oneHundredTwelveDF_25919 : Nat.Prime 25919 := by norm_num

private theorem prime_oneHundredTwelveDF_27367 : Nat.Prime 27367 := by norm_num

private theorem prime_oneHundredTwelveDF_27457 : Nat.Prime 27457 := by norm_num

private theorem prime_oneHundredTwelveDF_27799 : Nat.Prime 27799 := by norm_num

private theorem prime_oneHundredTwelveDF_27803 : Nat.Prime 27803 := by norm_num

private theorem prime_oneHundredTwelveDF_29251 : Nat.Prime 29251 := by norm_num

private theorem prime_oneHundredTwelveDF_29327 : Nat.Prime 29327 := by norm_num

private theorem prime_oneHundredTwelveDF_29483 : Nat.Prime 29483 := by norm_num

private theorem prime_oneHundredTwelveDF_29671 : Nat.Prime 29671 := by norm_num

private theorem prime_oneHundredTwelveDF_31319 : Nat.Prime 31319 := by norm_num

private theorem prime_oneHundredTwelveDF_31337 : Nat.Prime 31337 := by norm_num

private theorem prime_oneHundredTwelveDF_31699 : Nat.Prime 31699 := by norm_num

private theorem prime_oneHundredTwelveDF_32261 : Nat.Prime 32261 := by norm_num

private theorem prime_oneHundredTwelveDF_32771 : Nat.Prime 32771 := by norm_num

private theorem prime_oneHundredTwelveDF_33023 : Nat.Prime 33023 := by norm_num

private theorem prime_oneHundredTwelveDF_36541 : Nat.Prime 36541 := by norm_num

private theorem prime_oneHundredTwelveDF_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredTwelveDF_38153 : Nat.Prime 38153 := by norm_num

private theorem prime_oneHundredTwelveDF_40499 : Nat.Prime 40499 := by norm_num

private theorem prime_oneHundredTwelveDF_42397 : Nat.Prime 42397 := by norm_num

private theorem prime_oneHundredTwelveDF_42943 : Nat.Prime 42943 := by norm_num

private theorem prime_oneHundredTwelveDF_44171 : Nat.Prime 44171 := by norm_num

private theorem prime_oneHundredTwelveDF_44773 : Nat.Prime 44773 := by norm_num

private theorem prime_oneHundredTwelveDF_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredTwelveDF_44893 : Nat.Prime 44893 := by norm_num

private theorem prime_oneHundredTwelveDF_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwelveDF_48491 : Nat.Prime 48491 := by norm_num

private theorem prime_oneHundredTwelveDF_49331 : Nat.Prime 49331 := by norm_num

private theorem prime_oneHundredTwelveDF_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredTwelveDF_55343 : Nat.Prime 55343 := by norm_num

private theorem prime_oneHundredTwelveDF_57773 : Nat.Prime 57773 := by norm_num

private theorem prime_oneHundredTwelveDF_63353 : Nat.Prime 63353 := by norm_num

private theorem prime_oneHundredTwelveDF_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredTwelveDF_65699 : Nat.Prime 65699 := by norm_num

private theorem prime_oneHundredTwelveDF_69457 : Nat.Prime 69457 := by norm_num

private theorem prime_oneHundredTwelveDF_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwelveDF_70379 : Nat.Prime 70379 := by norm_num

private theorem prime_oneHundredTwelveDF_71867 : Nat.Prime 71867 := by norm_num

private theorem prime_oneHundredTwelveDF_71983 : Nat.Prime 71983 := by norm_num

private theorem prime_oneHundredTwelveDF_72613 : Nat.Prime 72613 := by norm_num

private theorem prime_oneHundredTwelveDF_74377 : Nat.Prime 74377 := by norm_num

private theorem prime_oneHundredTwelveDF_80279 : Nat.Prime 80279 := by norm_num

private theorem prime_oneHundredTwelveDF_82837 : Nat.Prime 82837 := by norm_num

private theorem prime_oneHundredTwelveDF_83933 : Nat.Prime 83933 := by norm_num

private theorem prime_oneHundredTwelveDF_92311 : Nat.Prime 92311 := by norm_num

private theorem prime_oneHundredTwelveDF_92369 : Nat.Prime 92369 := by norm_num

private theorem prime_oneHundredTwelveDF_99839 : Nat.Prime 99839 := by norm_num

private theorem prime_oneHundredTwelveDF_100801 : Nat.Prime 100801 := by norm_num

private theorem prime_oneHundredTwelveDF_100829 : Nat.Prime 100829 := by norm_num

private theorem prime_oneHundredTwelveDF_108761 : Nat.Prime 108761 := by norm_num

private theorem prime_oneHundredTwelveDF_111611 : Nat.Prime 111611 := by norm_num

private theorem prime_oneHundredTwelveDF_124601 : Nat.Prime 124601 := by norm_num

private theorem prime_oneHundredTwelveDF_124679 : Nat.Prime 124679 := by norm_num

private theorem prime_oneHundredTwelveDF_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredTwelveDF_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredTwelveDF_150107 : Nat.Prime 150107 := by norm_num

private theorem prime_oneHundredTwelveDF_151787 : Nat.Prime 151787 := by norm_num

private theorem prime_oneHundredTwelveDF_162971 : Nat.Prime 162971 := by norm_num

private theorem prime_oneHundredTwelveDF_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredTwelveDF_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwelveDF_179099 : Nat.Prime 179099 := by norm_num

private theorem prime_oneHundredTwelveDF_191123 : Nat.Prime 191123 := by norm_num

private theorem prime_oneHundredTwelveDF_193597 : Nat.Prime 193597 := by norm_num

private theorem prime_oneHundredTwelveDF_196051 : Nat.Prime 196051 := by norm_num

private theorem prime_oneHundredTwelveDF_207197 : Nat.Prime 207197 := by norm_num

private theorem prime_oneHundredTwelveDF_207341 : Nat.Prime 207341 := by norm_num

private theorem prime_oneHundredTwelveDF_222839 : Nat.Prime 222839 := by norm_num

private theorem prime_oneHundredTwelveDF_224221 : Nat.Prime 224221 := by norm_num

private theorem prime_oneHundredTwelveDF_242989 : Nat.Prime 242989 := by norm_num

private theorem prime_oneHundredTwelveDF_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredTwelveDF_246209 : Nat.Prime 246209 := by norm_num

private theorem prime_oneHundredTwelveDF_248483 : Nat.Prime 248483 := by norm_num

private theorem prime_oneHundredTwelveDF_249397 : Nat.Prime 249397 := by norm_num

private theorem prime_oneHundredTwelveDF_252583 : Nat.Prime 252583 := by norm_num

private theorem prime_oneHundredTwelveDF_261127 : Nat.Prime 261127 := by norm_num

private theorem prime_oneHundredTwelveDF_262519 : Nat.Prime 262519 := by norm_num

private theorem prime_oneHundredTwelveDF_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredTwelveDF_272809 : Nat.Prime 272809 := by norm_num

private theorem prime_oneHundredTwelveDF_277577 : Nat.Prime 277577 := by norm_num

private theorem prime_oneHundredTwelveDF_286073 : Nat.Prime 286073 := by norm_num

private theorem prime_oneHundredTwelveDF_296489 : Nat.Prime 296489 := by norm_num

private theorem prime_oneHundredTwelveDF_317189 : Nat.Prime 317189 := by norm_num

private theorem prime_oneHundredTwelveDF_317227 : Nat.Prime 317227 := by norm_num

private theorem prime_oneHundredTwelveDF_318473 : Nat.Prime 318473 := by norm_num

private theorem prime_oneHundredTwelveDF_339649 : Nat.Prime 339649 := by norm_num

private theorem prime_oneHundredTwelveDF_341863 : Nat.Prime 341863 := by norm_num

private theorem prime_oneHundredTwelveDF_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredTwelveDF_374047 : Nat.Prime 374047 := by norm_num

private theorem prime_oneHundredTwelveDF_383657 : Nat.Prime 383657 := by norm_num

private theorem prime_oneHundredTwelveDF_391451 : Nat.Prime 391451 := by norm_num

private theorem prime_oneHundredTwelveDF_405157 : Nat.Prime 405157 := by norm_num

private theorem prime_oneHundredTwelveDF_423103 : Nat.Prime 423103 := by norm_num

private theorem prime_oneHundredTwelveDF_435881 : Nat.Prime 435881 := by norm_num

private theorem prime_oneHundredTwelveDF_449347 : Nat.Prime 449347 := by norm_num

private theorem prime_oneHundredTwelveDF_452957 : Nat.Prime 452957 := by norm_num

private theorem prime_oneHundredTwelveDF_454799 : Nat.Prime 454799 := by norm_num

private theorem prime_oneHundredTwelveDF_553601 : Nat.Prime 553601 := by norm_num

private theorem prime_oneHundredTwelveDF_560969 : Nat.Prime 560969 := by norm_num

private theorem prime_oneHundredTwelveDF_562273 : Nat.Prime 562273 := by norm_num

private theorem prime_oneHundredTwelveDF_603613 : Nat.Prime 603613 := by norm_num

private theorem prime_oneHundredTwelveDF_611953 : Nat.Prime 611953 := by norm_num

private theorem prime_oneHundredTwelveDF_625627 : Nat.Prime 625627 := by norm_num

private theorem prime_oneHundredTwelveDF_633623 : Nat.Prime 633623 := by norm_num

private theorem prime_oneHundredTwelveDF_651109 : Nat.Prime 651109 := by norm_num

private theorem prime_oneHundredTwelveDF_653647 : Nat.Prime 653647 := by norm_num

private theorem prime_oneHundredTwelveDF_694979 : Nat.Prime 694979 := by norm_num

private theorem prime_oneHundredTwelveDF_729607 : Nat.Prime 729607 := by norm_num

private theorem prime_oneHundredTwelveDF_773693 : Nat.Prime 773693 := by norm_num

private theorem prime_oneHundredTwelveDF_789611 : Nat.Prime 789611 := by norm_num

private theorem prime_oneHundredTwelveDF_800909 : Nat.Prime 800909 := by norm_num

private theorem prime_oneHundredTwelveDF_825029 : Nat.Prime 825029 := by norm_num

private theorem prime_oneHundredTwelveDF_857453 : Nat.Prime 857453 := by norm_num

private theorem prime_oneHundredTwelveDF_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredTwelveDF_905581 : Nat.Prime 905581 := by norm_num

private theorem prime_oneHundredTwelveDF_937243 : Nat.Prime 937243 := by norm_num

private theorem prime_oneHundredTwelveDF_937331 : Nat.Prime 937331 := by norm_num

private theorem prime_oneHundredTwelveDF_1147231 : Nat.Prime 1147231 := by norm_num

private theorem prime_oneHundredTwelveDF_1171981 : Nat.Prime 1171981 := by norm_num

private theorem prime_oneHundredTwelveDF_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredTwelveDF_1233371 : Nat.Prime 1233371 := by norm_num

private theorem prime_oneHundredTwelveDF_1311311 : Nat.Prime 1311311 := by norm_num

private theorem prime_oneHundredTwelveDF_1445569 : Nat.Prime 1445569 := by norm_num

private theorem prime_oneHundredTwelveDF_1454081 : Nat.Prime 1454081 := by norm_num

private theorem prime_oneHundredTwelveDF_1508063 : Nat.Prime 1508063 := by norm_num

private theorem prime_oneHundredTwelveDF_1536649 : Nat.Prime 1536649 := by norm_num

private theorem prime_oneHundredTwelveDF_1545121 : Nat.Prime 1545121 := by norm_num

private theorem prime_oneHundredTwelveDF_1591813 : Nat.Prime 1591813 := by norm_num

private theorem prime_oneHundredTwelveDF_1592737 : Nat.Prime 1592737 := by norm_num

private theorem prime_oneHundredTwelveDF_1636529 : Nat.Prime 1636529 := by norm_num

private theorem prime_oneHundredTwelveDF_1651151 : Nat.Prime 1651151 := by norm_num

private theorem prime_oneHundredTwelveDF_1731589 : Nat.Prime 1731589 := by norm_num

private theorem prime_oneHundredTwelveDF_1747783 : Nat.Prime 1747783 := by norm_num

private theorem prime_oneHundredTwelveDF_2128177 : Nat.Prime 2128177 := by norm_num

private theorem prime_oneHundredTwelveDF_2129689 : Nat.Prime 2129689 := by norm_num

private theorem prime_oneHundredTwelveDF_2215537 : Nat.Prime 2215537 := by norm_num

private theorem prime_oneHundredTwelveDF_2286437 : Nat.Prime 2286437 := by norm_num

private theorem prime_oneHundredTwelveDF_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredTwelveDF_2506583 : Nat.Prime 2506583 := by norm_num

private theorem prime_oneHundredTwelveDF_2507777 : Nat.Prime 2507777 := by norm_num

private theorem prime_oneHundredTwelveDF_2585293 : Nat.Prime 2585293 := by norm_num

private theorem prime_oneHundredTwelveDF_2606969 : Nat.Prime 2606969 := by norm_num

private theorem prime_oneHundredTwelveDF_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredTwelveDF_2858179 : Nat.Prime 2858179 := by norm_num

private theorem prime_oneHundredTwelveDF_3171089 : Nat.Prime 3171089 := by norm_num

private theorem prime_oneHundredTwelveDF_3249863 : Nat.Prime 3249863 := by norm_num

private theorem prime_oneHundredTwelveDF_3384179 : Nat.Prime 3384179 := by norm_num

private theorem prime_oneHundredTwelveDF_3420499 : Nat.Prime 3420499 := by norm_num

private theorem prime_oneHundredTwelveDF_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredTwelveDF_3747979 : Nat.Prime 3747979 := by norm_num

private theorem prime_oneHundredTwelveDF_3756671 : Nat.Prime 3756671 := by norm_num

private theorem prime_oneHundredTwelveDF_3828269 : Nat.Prime 3828269 := by norm_num

private theorem prime_oneHundredTwelveDF_4003579 : Nat.Prime 4003579 := by norm_num

private theorem prime_oneHundredTwelveDF_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredTwelveDF_4313851 : Nat.Prime 4313851 := by norm_num

private theorem prime_oneHundredTwelveDF_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredTwelveDF_4474849 : Nat.Prime 4474849 := by norm_num

private theorem prime_oneHundredTwelveDF_4562083 : Nat.Prime 4562083 := by norm_num

private theorem prime_oneHundredTwelveDF_5318063 : Nat.Prime 5318063 := by norm_num

private theorem prime_oneHundredTwelveDF_5713181 : Nat.Prime 5713181 := by norm_num

private theorem prime_oneHundredTwelveDF_5770649 : Nat.Prime 5770649 := by norm_num

private theorem prime_oneHundredTwelveDF_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredTwelveDF_7155503 : Nat.Prime 7155503 := by norm_num

private theorem prime_oneHundredTwelveDF_7306177 : Nat.Prime 7306177 := by norm_num

private theorem prime_oneHundredTwelveDF_7592203 : Nat.Prime 7592203 := by norm_num

private theorem prime_oneHundredTwelveDF_8141093 : Nat.Prime 8141093 := by norm_num

private theorem prime_oneHundredTwelveDF_8273333 : Nat.Prime 8273333 := by norm_num

private theorem prime_oneHundredTwelveDF_8734511 : Nat.Prime 8734511 := by norm_num

private theorem prime_oneHundredTwelveDF_8751781 : Nat.Prime 8751781 := by norm_num

private theorem prime_oneHundredTwelveDF_9646093 : Nat.Prime 9646093 := by norm_num

private theorem prime_oneHundredTwelveDF_9877709 : Nat.Prime 9877709 := by norm_num

private theorem prime_oneHundredTwelveDF_10702079 : Nat.Prime 10702079 := by norm_num

private theorem prime_oneHundredTwelveDF_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwelveDF_12983963 : Nat.Prime 12983963 := by norm_num

private theorem prime_oneHundredTwelveDF_13511921 : Nat.Prime 13511921 := by norm_num

private theorem prime_oneHundredTwelveDF_14017337 : Nat.Prime 14017337 := by norm_num

private theorem prime_oneHundredTwelveDF_15206419 : Nat.Prime 15206419 := by norm_num

private theorem prime_oneHundredTwelveDF_15826513 : Nat.Prime 15826513 := by norm_num

private theorem prime_oneHundredTwelveDF_15971843 : Nat.Prime 15971843 := by norm_num

private theorem prime_oneHundredTwelveDF_16380781 : Nat.Prime 16380781 := by norm_num

private theorem prime_oneHundredTwelveDF_17086117 : Nat.Prime 17086117 := by norm_num

private theorem prime_oneHundredTwelveDF_17153117 : Nat.Prime 17153117 := by norm_num

private theorem prime_oneHundredTwelveDF_17343101 : Nat.Prime 17343101 := by norm_num

private theorem prime_oneHundredTwelveDF_17355509 : Nat.Prime 17355509 := by norm_num

private theorem prime_oneHundredTwelveDF_19038707 : Nat.Prime 19038707 := by norm_num

private theorem prime_oneHundredTwelveDF_19351279 : Nat.Prime 19351279 := by norm_num

private theorem prime_oneHundredTwelveDF_20256349 : Nat.Prime 20256349 := by norm_num

private theorem prime_oneHundredTwelveDF_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredTwelveDF_20838439 : Nat.Prime 20838439 := by norm_num

private theorem prime_oneHundredTwelveDF_21727217 : Nat.Prime 21727217 := by norm_num

private theorem prime_oneHundredTwelveDF_22929341 : Nat.Prime 22929341 := by norm_num

private theorem prime_oneHundredTwelveDF_24306859 : Nat.Prime 24306859 := by norm_num

private theorem prime_oneHundredTwelveDF_24766967 : Nat.Prime 24766967 := by norm_num

private theorem prime_oneHundredTwelveDF_26655217 : Nat.Prime 26655217 := by norm_num

private theorem prime_oneHundredTwelveDF_26895587 : Nat.Prime 26895587 := by norm_num

private theorem prime_oneHundredTwelveDF_27362917 : Nat.Prime 27362917 := by norm_num

private theorem prime_oneHundredTwelveDF_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_73
      · exact prime_oneHundredTwelveDF_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_33280867 : Nat.Prime 33280867 := by
  apply lucas_primality 33280867 (2 : ZMod 33280867)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (108761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (108761, 1)] : List FactorBlock).map factorBlockValue).prod) = 33280867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_108761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33280867) ^ 16640433 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33280867) ^ 11093622 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33280867) ^ 1957698 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33280867) ^ 306 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_37479791 : Nat.Prime 37479791 := by
  apply lucas_primality 37479791 (13 : ZMod 37479791)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3747979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3747979, 1)] : List FactorBlock).map factorBlockValue).prod) = 37479791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_3747979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 37479791) ^ 18739895 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 37479791) ^ 7495958 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 37479791) ^ 10 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_37882631 : Nat.Prime 37882631 := by
  apply lucas_primality 37882631 (26 : ZMod 37882631)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (222839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (222839, 1)] : List FactorBlock).map factorBlockValue).prod) = 37882631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_222839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 37882631) ^ 18941315 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (26 : ZMod 37882631) ^ 7576526 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (26 : ZMod 37882631) ^ 2228390 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (26 : ZMod 37882631) ^ 170 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_41446439 : Nat.Prime 41446439 := by
  apply lucas_primality 41446439 (11 : ZMod 41446439)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (59, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (59, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 41446439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_59
      · exact prime_oneHundredTwelveDF_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 41446439) ^ 20723219 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 41446439) ^ 3767858 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 41446439) ^ 1120174 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 41446439) ^ 702482 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 41446439) ^ 48026 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_43089581 : Nat.Prime 43089581 := by
  apply lucas_primality 43089581 (3 : ZMod 43089581)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (283, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (283, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 43089581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_283
      · exact prime_oneHundredTwelveDF_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43089581) ^ 21544790 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43089581) ^ 8617916 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43089581) ^ 1873460 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43089581) ^ 152260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 43089581) ^ 130180 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_43213957 : Nat.Prime 43213957 := by
  apply lucas_primality 43213957 (5 : ZMod 43213957)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (49331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (49331, 1)] : List FactorBlock).map factorBlockValue).prod) = 43213957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_73
      · exact prime_oneHundredTwelveDF_49331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43213957) ^ 21606978 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43213957) ^ 14404652 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43213957) ^ 591972 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 43213957) ^ 876 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_45994279 : Nat.Prime 45994279 := by
  apply lucas_primality 45994279 (3 : ZMod 45994279)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) = 45994279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_63353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45994279) ^ 22997139 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 15331426 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 4181298 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 726 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_46501019 : Nat.Prime 46501019 := by
  apply lucas_primality 46501019 (2 : ZMod 46501019)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) = 46501019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_71983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46501019) ^ 23250509 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2735354 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2447422 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 646 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_49072139 : Nat.Prime 49072139 := by
  apply lucas_primality 49072139 (2 : ZMod 49072139)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (271, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (271, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) = 49072139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_271
      · exact prime_oneHundredTwelveDF_2447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49072139) ^ 24536069 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49072139) ^ 1326274 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49072139) ^ 181078 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 49072139) ^ 20054 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_50390149 : Nat.Prime 50390149 := by
  apply lucas_primality 50390149 (2 : ZMod 50390149)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (41, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (41, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 50390149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_61
      · exact prime_oneHundredTwelveDF_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50390149) ^ 25195074 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 16796716 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 2190876 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 1229028 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 826068 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 690276 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_51637099 : Nat.Prime 51637099 := by
  apply lucas_primality 51637099 (2 : ZMod 51637099)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (452957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (452957, 1)] : List FactorBlock).map factorBlockValue).prod) = 51637099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_452957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51637099) ^ 25818549 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51637099) ^ 17212366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51637099) ^ 2717742 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 51637099) ^ 114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_52510687 : Nat.Prime 52510687 := by
  apply lucas_primality 52510687 (5 : ZMod 52510687)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) = 52510687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_8751781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52510687) ^ 26255343 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 17503562 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 6 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_55849597 : Nat.Prime 55849597 := by
  apply lucas_primality 55849597 (2 : ZMod 55849597)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (423103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (423103, 1)] : List FactorBlock).map factorBlockValue).prod) = 55849597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_423103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55849597) ^ 27924798 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55849597) ^ 18616532 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55849597) ^ 5077236 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 55849597) ^ 132 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1811
      · exact prime_oneHundredTwelveDF_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_74959583 : Nat.Prime 74959583 := by
  apply lucas_primality 74959583 (5 : ZMod 74959583)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37479791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37479791, 1)] : List FactorBlock).map factorBlockValue).prod) = 74959583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_37479791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 74959583) ^ 37479791 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 74959583) ^ 2 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_78489083 : Nat.Prime 78489083 := by
  apply lucas_primality 78489083 (2 : ZMod 78489083)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (800909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (800909, 1)] : List FactorBlock).map factorBlockValue).prod) = 78489083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_800909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78489083) ^ 39244541 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78489083) ^ 11212726 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78489083) ^ 98 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_79763389 : Nat.Prime 79763389 := by
  apply lucas_primality 79763389 (2 : ZMod 79763389)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 79763389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_71
      · exact prime_oneHundredTwelveDF_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79763389) ^ 39881694 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 26587796 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 4691964 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 1123428 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 14484 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_97204621 : Nat.Prime 97204621 := by
  apply lucas_primality 97204621 (6 : ZMod 97204621)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83, 1), (131, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83, 1), (131, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 97204621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_131
      · exact prime_oneHundredTwelveDF_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 97204621) ^ 48602310 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 97204621) ^ 32401540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 97204621) ^ 19440924 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 97204621) ^ 1171140 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 97204621) ^ 742020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 97204621) ^ 652380 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_131511187 : Nat.Prime 131511187 := by
  apply lucas_primality 131511187 (2 : ZMod 131511187)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7306177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7306177, 1)] : List FactorBlock).map factorBlockValue).prod) = 131511187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7306177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131511187) ^ 65755593 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 131511187) ^ 43837062 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 131511187) ^ 18 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_148903877 : Nat.Prime 148903877 := by
  apply lucas_primality 148903877 (2 : ZMod 148903877)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3384179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3384179, 1)] : List FactorBlock).map factorBlockValue).prod) = 148903877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_3384179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 148903877) ^ 74451938 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 148903877) ^ 13536716 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 148903877) ^ 44 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_158265131 : Nat.Prime 158265131 := by
  apply lucas_primality 158265131 (2 : ZMod 158265131)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158265131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_15826513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158265131) ^ 79132565 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 31653026 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 10 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_164472251 : Nat.Prime 164472251 := by
  apply lucas_primality 164472251 (2 : ZMod 164472251)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (53, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (53, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) = 164472251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_53
      · exact prime_oneHundredTwelveDF_12413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164472251) ^ 82236125 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 32894450 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 3103250 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 13250 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_174305903 : Nat.Prime 174305903 := by
  apply lucas_primality 174305903 (5 : ZMod 174305903)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (374047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 174305903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_233
      · exact prime_oneHundredTwelveDF_374047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 174305903) ^ 87152951 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 174305903) ^ 748094 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 174305903) ^ 466 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_236016889 : Nat.Prime 236016889 := by
  apply lucas_primality 236016889 (7 : ZMod 236016889)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (317227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (317227, 1)] : List FactorBlock).map factorBlockValue).prod) = 236016889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_317227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 236016889) ^ 118008444 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 236016889) ^ 78672296 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 236016889) ^ 7613448 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 236016889) ^ 744 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_248129153 : Nat.Prime 248129153 := by
  apply lucas_primality 248129153 (3 : ZMod 248129153)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 248129153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_89
      · exact prime_oneHundredTwelveDF_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 248129153) ^ 124064576 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 10788224 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 2787968 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 262016 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_251572669 : Nat.Prime 251572669 := by
  apply lucas_primality 251572669 (2 : ZMod 251572669)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (252583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (252583, 1)] : List FactorBlock).map factorBlockValue).prod) = 251572669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_252583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 251572669) ^ 125786334 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572669) ^ 83857556 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572669) ^ 3030996 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572669) ^ 996 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_266552171 : Nat.Prime 266552171 := by
  apply lucas_primality 266552171 (2 : ZMod 266552171)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) = 266552171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_26655217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 266552171) ^ 133276085 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 53310434 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 10 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_305169131 : Nat.Prime 305169131 := by
  apply lucas_primality 305169131 (2 : ZMod 305169131)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (857, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (857, 1), (5087, 1)] : List FactorBlock).map factorBlockValue).prod) = 305169131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_857
      · exact prime_oneHundredTwelveDF_5087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 305169131) ^ 152584565 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 305169131) ^ 61033826 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 305169131) ^ 43595590 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 305169131) ^ 356090 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 305169131) ^ 59990 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_317045479 : Nat.Prime 317045479 := by
  apply lucas_primality 317045479 (6 : ZMod 317045479)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (149, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (149, 1), (907, 1)] : List FactorBlock).map factorBlockValue).prod) = 317045479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_149
      · exact prime_oneHundredTwelveDF_907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 317045479) ^ 158522739 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 317045479) ^ 105681826 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 317045479) ^ 18649734 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 317045479) ^ 13784586 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 317045479) ^ 2127822 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 317045479) ^ 349554 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_319053557 : Nat.Prime 319053557 := by
  apply lucas_primality 319053557 (2 : ZMod 319053557)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) = 319053557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_79763389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 319053557) ^ 159526778 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 319053557) ^ 4 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_384652063 : Nat.Prime 384652063 := by
  apply lucas_primality 384652063 (5 : ZMod 384652063)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (196051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (196051, 1)] : List FactorBlock).map factorBlockValue).prod) = 384652063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_196051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 384652063) ^ 192326031 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 128217354 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 3528918 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 1962 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_424324643 : Nat.Prime 424324643 := by
  apply lucas_primality 424324643 (2 : ZMod 424324643)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 424324643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_79
      · exact prime_oneHundredTwelveDF_383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 424324643) ^ 212162321 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 424324643) ^ 60617806 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 424324643) ^ 5371198 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 424324643) ^ 1106 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_457396609 : Nat.Prime 457396609 := by
  apply lucas_primality 457396609 (7 : ZMod 457396609)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) = 457396609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_349
      · exact prime_oneHundredTwelveDF_3413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 457396609) ^ 228698304 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 152465536 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 1310592 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 134016 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_515196217 : Nat.Prime 515196217 := by
  apply lucas_primality 515196217 (5 : ZMod 515196217)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7155503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7155503, 1)] : List FactorBlock).map factorBlockValue).prod) = 515196217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7155503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 515196217) ^ 257598108 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 515196217) ^ 171732072 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 515196217) ^ 72 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_545326447 : Nat.Prime 545326447 := by
  apply lucas_primality 545326447 (6 : ZMod 545326447)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) = 545326447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_12983963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 545326447) ^ 272663223 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 181775482 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 77903778 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 42 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_681053033 : Nat.Prime 681053033 := by
  apply lucas_primality 681053033 (3 : ZMod 681053033)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2081, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2081, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) = 681053033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_2081
      · exact prime_oneHundredTwelveDF_3719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 681053033) ^ 340526516 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 681053033) ^ 61913912 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 681053033) ^ 327272 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 681053033) ^ 183128 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_711506639 : Nat.Prime 711506639 := by
  apply lucas_primality 711506639 (7 : ZMod 711506639)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (8273333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (8273333, 1)] : List FactorBlock).map factorBlockValue).prod) = 711506639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_8273333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 711506639) ^ 355753319 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 711506639) ^ 16546666 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 711506639) ^ 86 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17203
      · exact prime_oneHundredTwelveDF_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_101
      · exact prime_oneHundredTwelveDF_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_750855029 : Nat.Prime 750855029 := by
  apply lucas_primality 750855029 (3 : ZMod 750855029)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (53, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (53, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) = 750855029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_53
      · exact prime_oneHundredTwelveDF_6571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 750855029) ^ 375427514 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 750855029) ^ 107265004 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 750855029) ^ 68259548 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 750855029) ^ 14167076 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 750855029) ^ 114268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_764417231 : Nat.Prime 764417231 := by
  apply lucas_primality 764417231 (7 : ZMod 764417231)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 764417231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_61
      · exact prime_oneHundredTwelveDF_97
      · exact prime_oneHundredTwelveDF_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 764417231) ^ 382208615 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 152883446 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 12531430 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 7880590 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 59170 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_825447703 : Nat.Prime 825447703 := by
  apply lucas_primality 825447703 (5 : ZMod 825447703)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (233, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (233, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) = 825447703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_173
      · exact prime_oneHundredTwelveDF_233
      · exact prime_oneHundredTwelveDF_3413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 825447703) ^ 412723851 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 825447703) ^ 275149234 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 825447703) ^ 4771374 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 825447703) ^ 3542694 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 825447703) ^ 241854 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_894423209 : Nat.Prime 894423209 := by
  apply lucas_primality 894423209 (3 : ZMod 894423209)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (15971843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (15971843, 1)] : List FactorBlock).map factorBlockValue).prod) = 894423209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_15971843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 894423209) ^ 447211604 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 894423209) ^ 127774744 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 894423209) ^ 56 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1120329107 : Nat.Prime 1120329107 := by
  apply lucas_primality 1120329107 (2 : ZMod 1120329107)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43089581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43089581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1120329107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_43089581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1120329107) ^ 560164553 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1120329107) ^ 86179162 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1120329107) ^ 26 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1139905313 : Nat.Prime 1139905313 := by
  apply lucas_primality 1139905313 (3 : ZMod 1139905313)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (13, 1), (391451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (13, 1), (391451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1139905313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_391451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1139905313) ^ 569952656 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139905313) ^ 162843616 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139905313) ^ 87685024 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1139905313) ^ 2912 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1180174613 : Nat.Prime 1180174613 := by
  apply lucas_primality 1180174613 (2 : ZMod 1180174613)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (17355509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (17355509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180174613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_17355509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1180174613) ^ 590087306 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180174613) ^ 69422036 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1180174613) ^ 68 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1197521651 : Nat.Prime 1197521651 := by
  apply lucas_primality 1197521651 (6 : ZMod 1197521651)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (17, 1), (29, 1), (37, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (17, 1), (29, 1), (37, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1197521651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1197521651) ^ 598760825 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 239504330 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 92117050 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 70442450 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 41293850 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 32365450 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1197521651) ^ 11856650 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1243393171 : Nat.Prime 1243393171 := by
  apply lucas_primality 1243393171 (10 : ZMod 1243393171)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41446439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41446439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243393171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_41446439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1243393171) ^ 621696585 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1243393171) ^ 414464390 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1243393171) ^ 248678634 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 1243393171) ^ 30 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_1667
      · exact prime_oneHundredTwelveDF_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1350641519 : Nat.Prime 1350641519 := by
  apply lucas_primality 1350641519 (13 : ZMod 1350641519)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (1651151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (1651151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1350641519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_409
      · exact prime_oneHundredTwelveDF_1651151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1350641519) ^ 675320759 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1350641519) ^ 3302302 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 1350641519) ^ 818 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1488692417 : Nat.Prime 1488692417 := by
  apply lucas_primality 1488692417 (3 : ZMod 1488692417)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (31, 1), (137, 1), (5477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (31, 1), (137, 1), (5477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1488692417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_137
      · exact prime_oneHundredTwelveDF_5477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1488692417) ^ 744346208 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1488692417) ^ 48022336 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1488692417) ^ 10866368 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1488692417) ^ 271808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1678038433 : Nat.Prime 1678038433 := by
  apply lucas_primality 1678038433 (5 : ZMod 1678038433)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678038433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1678038433) ^ 839019216 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 559346144 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 239719776 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 54130272 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 15394848 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 2270688 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1769124349 : Nat.Prime 1769124349 := by
  apply lucas_primality 1769124349 (2 : ZMod 1769124349)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (16380781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (16380781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769124349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_16380781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1769124349) ^ 884562174 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769124349) ^ 589708116 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769124349) ^ 108 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1791295669 : Nat.Prime 1791295669 := by
  apply lucas_primality 1791295669 (2 : ZMod 1791295669)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (223, 1), (74377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (223, 1), (74377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1791295669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_223
      · exact prime_oneHundredTwelveDF_74377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1791295669) ^ 895647834 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1791295669) ^ 597098556 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1791295669) ^ 8032716 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1791295669) ^ 24084 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1815083779 : Nat.Prime 1815083779 := by
  apply lucas_primality 1815083779 (3 : ZMod 1815083779)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1815083779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_773693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1815083779) ^ 907541889 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 605027926 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 106769634 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 78916686 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 2346 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1946792983 : Nat.Prime 1946792983 := by
  apply lucas_primality 1946792983 (3 : ZMod 1946792983)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1301, 1), (249397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1301, 1), (249397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1946792983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_1301
      · exact prime_oneHundredTwelveDF_249397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1946792983) ^ 973396491 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 648930994 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 1496382 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 7806 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1953042799 : Nat.Prime 1953042799 := by
  apply lucas_primality 1953042799 (3 : ZMod 1953042799)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953042799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_46501019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1953042799) ^ 976521399 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 651014266 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 279006114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 42 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1971558053 : Nat.Prime 1971558053 := by
  apply lucas_primality 1971558053 (2 : ZMod 1971558053)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (757, 1), (651109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (757, 1), (651109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1971558053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_757
      · exact prime_oneHundredTwelveDF_651109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1971558053) ^ 985779026 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971558053) ^ 2604436 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971558053) ^ 3028 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2017690943 : Nat.Prime 2017690943 := by
  apply lucas_primality 2017690943 (5 : ZMod 2017690943)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (503, 1), (10181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (503, 1), (10181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2017690943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_197
      · exact prime_oneHundredTwelveDF_503
      · exact prime_oneHundredTwelveDF_10181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2017690943) ^ 1008845471 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2017690943) ^ 10242086 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2017690943) ^ 4011314 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2017690943) ^ 198182 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_71
      · exact prime_oneHundredTwelveDF_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2977549837 : Nat.Prime 2977549837 := by
  apply lucas_primality 2977549837 (2 : ZMod 2977549837)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977549837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_248129153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2977549837) ^ 1488774918 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 992516612 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 12 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3017214619 : Nat.Prime 3017214619 := by
  apply lucas_primality 3017214619 (3 : ZMod 3017214619)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 3), (67, 1), (5639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 3), (67, 1), (5639, 1)] : List FactorBlock).map factorBlockValue).prod) = 3017214619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_67
      · exact prime_oneHundredTwelveDF_5639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3017214619) ^ 1508607309 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3017214619) ^ 1005738206 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3017214619) ^ 274292238 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3017214619) ^ 45033054 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3017214619) ^ 535062 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3018872029 : Nat.Prime 3018872029 := by
  apply lucas_primality 3018872029 (2 : ZMod 3018872029)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (251572669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (251572669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3018872029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_251572669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3018872029) ^ 1509436014 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3018872029) ^ 1006290676 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3018872029) ^ 12 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3535965571 : Nat.Prime 3535965571 := by
  apply lucas_primality 3535965571 (2 : ZMod 3535965571)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (2507777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (2507777, 1)] : List FactorBlock).map factorBlockValue).prod) = 3535965571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_2507777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3535965571) ^ 1767982785 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535965571) ^ 1178655190 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535965571) ^ 707193114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535965571) ^ 75233310 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3535965571) ^ 1410 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3893692381 : Nat.Prime 3893692381 := by
  apply lucas_primality 3893692381 (2 : ZMod 3893692381)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (859, 1), (2437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (859, 1), (2437, 1)] : List FactorBlock).map factorBlockValue).prod) = 3893692381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_859
      · exact prime_oneHundredTwelveDF_2437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3893692381) ^ 1946846190 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3893692381) ^ 1297897460 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3893692381) ^ 778738476 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3893692381) ^ 125602980 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3893692381) ^ 4532820 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3893692381) ^ 1597740 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4276278527 : Nat.Prime 4276278527 := by
  apply lucas_primality 4276278527 (5 : ZMod 4276278527)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (164472251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (164472251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4276278527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_164472251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4276278527) ^ 2138139263 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276278527) ^ 328944502 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276278527) ^ 26 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4449030959 : Nat.Prime 4449030959 := by
  apply lucas_primality 4449030959 (7 : ZMod 4449030959)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (7592203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (7592203, 1)] : List FactorBlock).map factorBlockValue).prod) = 4449030959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_293
      · exact prime_oneHundredTwelveDF_7592203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4449030959) ^ 2224515479 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 4449030959) ^ 15184406 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 4449030959) ^ 586 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4464915347 : Nat.Prime 4464915347 := by
  apply lucas_primality 4464915347 (2 : ZMod 4464915347)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1049, 1), (2128177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1049, 1), (2128177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4464915347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1049
      · exact prime_oneHundredTwelveDF_2128177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4464915347) ^ 2232457673 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4464915347) ^ 4256354 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4464915347) ^ 2098 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4725961831 : Nat.Prime 4725961831 := by
  apply lucas_primality 4725961831 (3 : ZMod 4725961831)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) = 4725961831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_52510687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4725961831) ^ 2362980915 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 1575320610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 945192366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 90 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4850466217 : Nat.Prime 4850466217 := by
  apply lucas_primality 4850466217 (10 : ZMod 4850466217)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (83, 1), (349, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (83, 1), (349, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) = 4850466217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_349
      · exact prime_oneHundredTwelveDF_6977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4850466217) ^ 2425233108 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4850466217) ^ 1616822072 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4850466217) ^ 58439352 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4850466217) ^ 13898184 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 4850466217) ^ 695208 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4853859953 : Nat.Prime 4853859953 := by
  apply lucas_primality 4853859953 (3 : ZMod 4853859953)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4853859953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_150107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4853859953) ^ 2426929976 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 112880464 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 103273616 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 32336 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_5151962171 : Nat.Prime 5151962171 := by
  apply lucas_primality 5151962171 (2 : ZMod 5151962171)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (515196217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (515196217, 1)] : List FactorBlock).map factorBlockValue).prod) = 5151962171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_515196217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5151962171) ^ 2575981085 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5151962171) ^ 1030392434 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5151962171) ^ 10 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_5260447481 : Nat.Prime 5260447481 := by
  apply lucas_primality 5260447481 (3 : ZMod 5260447481)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131511187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131511187, 1)] : List FactorBlock).map factorBlockValue).prod) = 5260447481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_131511187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5260447481) ^ 2630223740 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5260447481) ^ 1052089496 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5260447481) ^ 40 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_5276183617 : Nat.Prime 5276183617 := by
  apply lucas_primality 5276183617 (7 : ZMod 5276183617)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5276183617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5276183617) ^ 2638091808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 1758727872 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 479653056 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 19008 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_5886061981 : Nat.Prime 5886061981 := by
  apply lucas_primality 5886061981 (18 : ZMod 5886061981)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) = 5886061981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_5770649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 5886061981) ^ 2943030990 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1962020660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1177212396 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 346238940 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_311
      · exact prime_oneHundredTwelveDF_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_7076497397 : Nat.Prime 7076497397 := by
  apply lucas_primality 7076497397 (2 : ZMod 7076497397)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1769124349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1769124349, 1)] : List FactorBlock).map factorBlockValue).prod) = 7076497397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1769124349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7076497397) ^ 3538248698 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7076497397) ^ 4 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_7334860081 : Nat.Prime 7334860081 := by
  apply lucas_primality 7334860081 (11 : ZMod 7334860081)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23, 2), (57773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23, 2), (57773, 1)] : List FactorBlock).map factorBlockValue).prod) = 7334860081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_57773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7334860081) ^ 3667430040 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 7334860081) ^ 2444953360 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 7334860081) ^ 1466972016 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 7334860081) ^ 318906960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 7334860081) ^ 126960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_8126659771 : Nat.Prime 8126659771 := by
  apply lucas_primality 8126659771 (3 : ZMod 8126659771)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 2), (937331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 2), (937331, 1)] : List FactorBlock).map factorBlockValue).prod) = 8126659771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_937331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8126659771) ^ 4063329885 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 2708886590 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 1625331954 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 478038810 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 8670 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_9786532061 : Nat.Prime 9786532061 := by
  apply lucas_primality 9786532061 (2 : ZMod 9786532061)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (193, 1), (997, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (193, 1), (997, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 9786532061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_193
      · exact prime_oneHundredTwelveDF_997
      · exact prime_oneHundredTwelveDF_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9786532061) ^ 4893266030 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9786532061) ^ 1957306412 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9786532061) ^ 50707420 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9786532061) ^ 9815980 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9786532061) ^ 3848420 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10303924343 : Nat.Prime 10303924343 := by
  apply lucas_primality 10303924343 (5 : ZMod 10303924343)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5151962171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5151962171, 1)] : List FactorBlock).map factorBlockValue).prod) = 10303924343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5151962171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10303924343) ^ 5151962171 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 10303924343) ^ 2 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10890763661 : Nat.Prime 10890763661 := by
  apply lucas_primality 10890763661 (2 : ZMod 10890763661)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (83, 1), (937243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (83, 1), (937243, 1)] : List FactorBlock).map factorBlockValue).prod) = 10890763661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_937243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10890763661) ^ 5445381830 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10890763661) ^ 2178152732 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10890763661) ^ 1555823380 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10890763661) ^ 131214020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10890763661) ^ 11620 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_11905824439 : Nat.Prime 11905824439 := by
  apply lucas_primality 11905824439 (3 : ZMod 11905824439)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (149, 1), (261127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (149, 1), (261127, 1)] : List FactorBlock).map factorBlockValue).prod) = 11905824439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_149
      · exact prime_oneHundredTwelveDF_261127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11905824439) ^ 5952912219 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 3968608146 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 700342614 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 79904862 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 45594 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_14011433063 : Nat.Prime 14011433063 := by
  apply lucas_primality 14011433063 (5 : ZMod 14011433063)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (22907, 1), (27803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (22907, 1), (27803, 1)] : List FactorBlock).map factorBlockValue).prod) = 14011433063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_22907
      · exact prime_oneHundredTwelveDF_27803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14011433063) ^ 7005716531 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14011433063) ^ 1273766642 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14011433063) ^ 611666 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 14011433063) ^ 503954 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_14026408709 : Nat.Prime 14026408709 := by
  apply lucas_primality 14026408709 (2 : ZMod 14026408709)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026408709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_3249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14026408709) ^ 7013204354 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 1078954516 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 168992876 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 4316 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_16691379371 : Nat.Prime 16691379371 := by
  apply lucas_primality 16691379371 (2 : ZMod 16691379371)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (27362917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (27362917, 1)] : List FactorBlock).map factorBlockValue).prod) = 16691379371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_61
      · exact prime_oneHundredTwelveDF_27362917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16691379371) ^ 8345689685 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16691379371) ^ 3338275874 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16691379371) ^ 273629170 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 16691379371) ^ 610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_23075790403 : Nat.Prime 23075790403 := by
  apply lucas_primality 23075790403 (2 : ZMod 23075790403)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (78489083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (78489083, 1)] : List FactorBlock).map factorBlockValue).prod) = 23075790403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_78489083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23075790403) ^ 11537895201 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23075790403) ^ 7691930134 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23075790403) ^ 3296541486 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 23075790403) ^ 294 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_26789492083 : Nat.Prime 26789492083 := by
  apply lucas_primality 26789492083 (5 : ZMod 26789492083)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4464915347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4464915347, 1)] : List FactorBlock).map factorBlockValue).prod) = 26789492083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_4464915347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26789492083) ^ 13394746041 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26789492083) ^ 8929830694 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26789492083) ^ 6 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_27190587233 : Nat.Prime 27190587233 := by
  apply lucas_primality 27190587233 (3 : ZMod 27190587233)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (1093, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (1093, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod) = 27190587233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_1093
      · exact prime_oneHundredTwelveDF_21011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27190587233) ^ 13595293616 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27190587233) ^ 734880736 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27190587233) ^ 24877024 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27190587233) ^ 1294112 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_27210680461 : Nat.Prime 27210680461 := by
  apply lucas_primality 27210680461 (2 : ZMod 27210680461)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (50390149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (50390149, 1)] : List FactorBlock).map factorBlockValue).prod) = 27210680461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_50390149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27210680461) ^ 13605340230 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 9070226820 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 5442136092 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_32887474027 : Nat.Prime 32887474027 := by
  apply lucas_primality 32887474027 (2 : ZMod 32887474027)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 3), (59, 1), (223, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 3), (59, 1), (223, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 32887474027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_59
      · exact prime_oneHundredTwelveDF_223
      · exact prime_oneHundredTwelveDF_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32887474027) ^ 16443737013 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32887474027) ^ 10962491342 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32887474027) ^ 2989770366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32887474027) ^ 557414814 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32887474027) ^ 147477462 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32887474027) ^ 105071802 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_37892057519 : Nat.Prime 37892057519 := by
  apply lucas_primality 37892057519 (7 : ZMod 37892057519)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (10993, 1), (246209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (10993, 1), (246209, 1)] : List FactorBlock).map factorBlockValue).prod) = 37892057519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_10993
      · exact prime_oneHundredTwelveDF_246209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37892057519) ^ 18946028759 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37892057519) ^ 5413151074 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37892057519) ^ 3446926 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37892057519) ^ 153902 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_41850003229 : Nat.Prime 41850003229 := by
  apply lucas_primality 41850003229 (2 : ZMod 41850003229)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (317045479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (317045479, 1)] : List FactorBlock).map factorBlockValue).prod) = 41850003229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_317045479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41850003229) ^ 20925001614 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41850003229) ^ 13950001076 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41850003229) ^ 3804545748 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41850003229) ^ 132 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_43581711557 : Nat.Prime 43581711557 := by
  apply lucas_primality 43581711557 (2 : ZMod 43581711557)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (211, 1), (51637099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (211, 1), (51637099, 1)] : List FactorBlock).map factorBlockValue).prod) = 43581711557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_211
      · exact prime_oneHundredTwelveDF_51637099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43581711557) ^ 21790855778 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43581711557) ^ 206548396 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 43581711557) ^ 844 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_45804445331 : Nat.Prime 45804445331 := by
  apply lucas_primality 45804445331 (2 : ZMod 45804445331)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (251, 1), (2606969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (251, 1), (2606969, 1)] : List FactorBlock).map factorBlockValue).prod) = 45804445331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_251
      · exact prime_oneHundredTwelveDF_2606969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45804445331) ^ 22902222665 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45804445331) ^ 9160889066 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45804445331) ^ 6543492190 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45804445331) ^ 182487830 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 45804445331) ^ 17570 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_68112244661 : Nat.Prime 68112244661 := by
  apply lucas_primality 68112244661 (2 : ZMod 68112244661)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (101, 1), (277, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (101, 1), (277, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) = 68112244661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_101
      · exact prime_oneHundredTwelveDF_277
      · exact prime_oneHundredTwelveDF_2969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68112244661) ^ 34056122330 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68112244661) ^ 13622448932 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68112244661) ^ 1661274260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68112244661) ^ 674378660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68112244661) ^ 245892580 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 68112244661) ^ 22941140 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_69578561869 : Nat.Prime 69578561869 := by
  apply lucas_primality 69578561869 (6 : ZMod 69578561869)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (305169131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (305169131, 1)] : List FactorBlock).map factorBlockValue).prod) = 69578561869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_305169131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 69578561869) ^ 34789280934 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 69578561869) ^ 23192853956 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 69578561869) ^ 3662029572 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 69578561869) ^ 228 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_87239226703 : Nat.Prime 87239226703 := by
  apply lucas_primality 87239226703 (3 : ZMod 87239226703)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (10781, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (10781, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) = 87239226703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_10781
      · exact prime_oneHundredTwelveDF_12373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87239226703) ^ 43619613351 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 29079742234 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 800359878 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 8091942 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 87239226703) ^ 7050774 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_93170621837 : Nat.Prime 93170621837 := by
  apply lucas_primality 93170621837 (2 : ZMod 93170621837)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227, 1), (823, 1), (124679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227, 1), (823, 1), (124679, 1)] : List FactorBlock).map factorBlockValue).prod) = 93170621837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_227
      · exact prime_oneHundredTwelveDF_823
      · exact prime_oneHundredTwelveDF_124679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93170621837) ^ 46585310918 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93170621837) ^ 410443268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93170621837) ^ 113208532 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 93170621837) ^ 747284 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_95065694189 : Nat.Prime 95065694189 := by
  apply lucas_primality 95065694189 (2 : ZMod 95065694189)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (109, 1), (5318063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (109, 1), (5318063, 1)] : List FactorBlock).map factorBlockValue).prod) = 95065694189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_5318063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95065694189) ^ 47532847094 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 95065694189) ^ 2318675468 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 95065694189) ^ 872162332 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 95065694189) ^ 17876 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_95520658789 : Nat.Prime 95520658789 := by
  apply lucas_primality 95520658789 (6 : ZMod 95520658789)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (36541, 1), (72613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (36541, 1), (72613, 1)] : List FactorBlock).map factorBlockValue).prod) = 95520658789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_36541
      · exact prime_oneHundredTwelveDF_72613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 95520658789) ^ 47760329394 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 31840219596 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 2614068 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 1315476 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_109736033929 : Nat.Prime 109736033929 := by
  apply lucas_primality 109736033929 (13 : ZMod 109736033929)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) = 109736033929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_3163
      · exact prime_oneHundredTwelveDF_1445569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 109736033929) ^ 54868016964 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 36578677976 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 34693656 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 75912 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_149634707627 : Nat.Prime 149634707627 := by
  apply lucas_primality 149634707627 (2 : ZMod 149634707627)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (236016889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (236016889, 1)] : List FactorBlock).map factorBlockValue).prod) = 149634707627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_317
      · exact prime_oneHundredTwelveDF_236016889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 149634707627) ^ 74817353813 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 149634707627) ^ 472033778 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 149634707627) ^ 634 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_89
      · exact prime_oneHundredTwelveDF_373
      · exact prime_oneHundredTwelveDF_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_169887150217 : Nat.Prime 169887150217 := by
  apply lucas_primality 169887150217 (10 : ZMod 169887150217)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (59, 1), (5713181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (59, 1), (5713181, 1)] : List FactorBlock).map factorBlockValue).prod) = 169887150217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_59
      · exact prime_oneHundredTwelveDF_5713181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 169887150217) ^ 84943575108 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 169887150217) ^ 56629050072 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 169887150217) ^ 24269592888 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 169887150217) ^ 2879443224 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 169887150217) ^ 29736 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_215565659143 : Nat.Prime 215565659143 := by
  apply lucas_primality 215565659143 (3 : ZMod 215565659143)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) = 215565659143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_764417231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215565659143) ^ 107782829571 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 71855219714 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 4586503386 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 282 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_229300624307 : Nat.Prime 229300624307 := by
  apply lucas_primality 229300624307 (2 : ZMod 229300624307)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (317, 1), (1636529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (317, 1), (1636529, 1)] : List FactorBlock).map factorBlockValue).prod) = 229300624307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_317
      · exact prime_oneHundredTwelveDF_1636529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 229300624307) ^ 114650312153 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229300624307) ^ 17638509562 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229300624307) ^ 13488272018 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229300624307) ^ 723345818 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 229300624307) ^ 140114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_243789649849 : Nat.Prime 243789649849 := by
  apply lucas_primality 243789649849 (17 : ZMod 243789649849)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3739, 1), (905581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3739, 1), (905581, 1)] : List FactorBlock).map factorBlockValue).prod) = 243789649849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_3739
      · exact prime_oneHundredTwelveDF_905581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 243789649849) ^ 121894824924 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 243789649849) ^ 81263216616 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 243789649849) ^ 65201832 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 243789649849) ^ 269208 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_273549391187 : Nat.Prime 273549391187 := by
  apply lucas_primality 273549391187 (2 : ZMod 273549391187)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (331, 1), (24306859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (331, 1), (24306859, 1)] : List FactorBlock).map factorBlockValue).prod) = 273549391187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_331
      · exact prime_oneHundredTwelveDF_24306859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 273549391187) ^ 136774695593 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273549391187) ^ 16091140658 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273549391187) ^ 826433206 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 273549391187) ^ 11254 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_324699246947 : Nat.Prime 324699246947 := by
  apply lucas_primality 324699246947 (2 : ZMod 324699246947)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) = 324699246947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_659
      · exact prime_oneHundredTwelveDF_1289
      · exact prime_oneHundredTwelveDF_191123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324699246947) ^ 162349623473 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 492715094 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 251900114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 1698902 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_326767152461 : Nat.Prime 326767152461 := by
  apply lucas_primality 326767152461 (2 : ZMod 326767152461)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (71, 1), (1019, 1), (32261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (71, 1), (1019, 1), (32261, 1)] : List FactorBlock).map factorBlockValue).prod) = 326767152461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_71
      · exact prime_oneHundredTwelveDF_1019
      · exact prime_oneHundredTwelveDF_32261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 326767152461) ^ 163383576230 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767152461) ^ 65353430492 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767152461) ^ 46681021780 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767152461) ^ 4602354260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767152461) ^ 320674340 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767152461) ^ 10128860 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_340078141943 : Nat.Prime 340078141943 := by
  apply lucas_primality 340078141943 (5 : ZMod 340078141943)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) = 340078141943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_881
      · exact prime_oneHundredTwelveDF_2506583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 340078141943) ^ 170039070971 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 48582591706 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 30916194722 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 386013782 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 135674 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_3931
      · exact prime_oneHundredTwelveDF_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_346024648097 : Nat.Prime 346024648097 := by
  apply lucas_primality 346024648097 (3 : ZMod 346024648097)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (59, 1), (9646093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (59, 1), (9646093, 1)] : List FactorBlock).map factorBlockValue).prod) = 346024648097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_59
      · exact prime_oneHundredTwelveDF_9646093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 346024648097) ^ 173012324048 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 346024648097) ^ 18211823584 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 346024648097) ^ 5864824544 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 346024648097) ^ 35872 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_362172069821 : Nat.Prime 362172069821 := by
  apply lucas_primality 362172069821 (2 : ZMod 362172069821)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (79, 1), (20838439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (79, 1), (20838439, 1)] : List FactorBlock).map factorBlockValue).prod) = 362172069821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_79
      · exact prime_oneHundredTwelveDF_20838439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 362172069821) ^ 181086034910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 72434413964 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 32924733620 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 4584456580 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 17380 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_399570089203 : Nat.Prime 399570089203 := by
  apply lucas_primality 399570089203 (2 : ZMod 399570089203)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (29, 1), (33280867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (29, 1), (33280867, 1)] : List FactorBlock).map factorBlockValue).prod) = 399570089203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_33280867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 399570089203) ^ 199785044601 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 399570089203) ^ 133190029734 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 399570089203) ^ 17372612574 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 399570089203) ^ 13778278938 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 399570089203) ^ 12006 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_604109755261 : Nat.Prime 604109755261 := by
  apply lucas_primality 604109755261 (10 : ZMod 604109755261)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 1), (31, 1), (827, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 1), (31, 1), (827, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) = 604109755261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_827
      · exact prime_oneHundredTwelveDF_3967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 604109755261) ^ 302054877630 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 201369918420 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 120821951052 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 54919068660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 19487411460 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 730483380 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 604109755261) ^ 152283780 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_695785618691 : Nat.Prime 695785618691 := by
  apply lucas_primality 695785618691 (2 : ZMod 695785618691)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (69578561869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (69578561869, 1)] : List FactorBlock).map factorBlockValue).prod) = 695785618691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_69578561869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695785618691) ^ 347892809345 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 695785618691) ^ 139157123738 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 695785618691) ^ 10 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_871261092881 : Nat.Prime 871261092881 := by
  apply lucas_primality 871261092881 (3 : ZMod 871261092881)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (10890763661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (10890763661, 1)] : List FactorBlock).map factorBlockValue).prod) = 871261092881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_10890763661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 871261092881) ^ 435630546440 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 871261092881) ^ 174252218576 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 871261092881) ^ 80 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_890831866621 : Nat.Prime 890831866621 := by
  apply lucas_primality 890831866621 (2 : ZMod 890831866621)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (181, 1), (1181, 1), (69457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (181, 1), (1181, 1), (69457, 1)] : List FactorBlock).map factorBlockValue).prod) = 890831866621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_181
      · exact prime_oneHundredTwelveDF_1181
      · exact prime_oneHundredTwelveDF_69457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 890831866621) ^ 445415933310 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 890831866621) ^ 296943955540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 890831866621) ^ 178166373324 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 890831866621) ^ 4921723020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 890831866621) ^ 754303020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 890831866621) ^ 12825660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_993048978323 : Nat.Prime 993048978323 := by
  apply lucas_primality 993048978323 (2 : ZMod 993048978323)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (27367, 1), (625627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (27367, 1), (625627, 1)] : List FactorBlock).map factorBlockValue).prod) = 993048978323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_27367
      · exact prime_oneHundredTwelveDF_625627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 993048978323) ^ 496524489161 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 993048978323) ^ 34243068218 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 993048978323) ^ 36286366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 993048978323) ^ 1587286 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1101402241151 : Nat.Prime 1101402241151 := by
  apply lucas_primality 1101402241151 (11 : ZMod 1101402241151)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (149, 1), (307, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (149, 1), (307, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101402241151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_149
      · exact prime_oneHundredTwelveDF_307
      · exact prime_oneHundredTwelveDF_397
      · exact prime_oneHundredTwelveDF_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1101402241151) ^ 550701120575 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1101402241151) ^ 220280448230 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1101402241151) ^ 7391961350 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1101402241151) ^ 3587629450 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1101402241151) ^ 2774312950 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1101402241151) ^ 907998550 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1194213614807 : Nat.Prime 1194213614807 := by
  apply lucas_primality 1194213614807 (5 : ZMod 1194213614807)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24109, 1), (24766967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24109, 1), (24766967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1194213614807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_24109
      · exact prime_oneHundredTwelveDF_24766967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1194213614807) ^ 597106807403 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1194213614807) ^ 49533934 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1194213614807) ^ 48218 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1362244893221 : Nat.Prime 1362244893221 := by
  apply lucas_primality 1362244893221 (2 : ZMod 1362244893221)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (68112244661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (68112244661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362244893221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_68112244661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1362244893221) ^ 681122446610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362244893221) ^ 272448978644 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362244893221) ^ 20 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1801134966187 : Nat.Prime 1801134966187 := by
  apply lucas_primality 1801134966187 (2 : ZMod 1801134966187)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801134966187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_5886061981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1801134966187) ^ 900567483093 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 600378322062 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 105949115658 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 306 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1959168993193 : Nat.Prime 1959168993193 := by
  apply lucas_primality 1959168993193 (7 : ZMod 1959168993193)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (27210680461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (27210680461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1959168993193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_27210680461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1959168993193) ^ 979584496596 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1959168993193) ^ 653056331064 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1959168993193) ^ 72 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2245139530429 : Nat.Prime 2245139530429 := by
  apply lucas_primality 2245139530429 (6 : ZMod 2245139530429)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (167, 1), (1120329107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (167, 1), (1120329107, 1)] : List FactorBlock).map factorBlockValue).prod) = 2245139530429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_167
      · exact prime_oneHundredTwelveDF_1120329107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2245139530429) ^ 1122569765214 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2245139530429) ^ 748379843476 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2245139530429) ^ 13443949284 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2245139530429) ^ 2004 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2486991238073 : Nat.Prime 2486991238073 := by
  apply lucas_primality 2486991238073 (3 : ZMod 2486991238073)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2486991238073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_859
      · exact prime_oneHundredTwelveDF_1731589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2486991238073) ^ 1243495619036 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 226090112552 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 130894275688 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 2895216808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 1436248 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3277510442819 : Nat.Prime 3277510442819 := by
  apply lucas_primality 3277510442819 (2 : ZMod 3277510442819)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (40499, 1), (2129689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (40499, 1), (2129689, 1)] : List FactorBlock).map factorBlockValue).prod) = 3277510442819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_40499
      · exact prime_oneHundredTwelveDF_2129689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3277510442819) ^ 1638755221409 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3277510442819) ^ 172500549622 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3277510442819) ^ 80928182 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3277510442819) ^ 1538962 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3281236476731 : Nat.Prime 3281236476731 := by
  apply lucas_primality 3281236476731 (6 : ZMod 3281236476731)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (23, 1), (750855029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (23, 1), (750855029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3281236476731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_750855029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3281236476731) ^ 1640618238365 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 3281236476731) ^ 656247295346 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 3281236476731) ^ 172696656670 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 3281236476731) ^ 142662455510 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 3281236476731) ^ 4370 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3353735554207 : Nat.Prime 3353735554207 := by
  apply lucas_primality 3353735554207 (3 : ZMod 3353735554207)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3353735554207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_757
      · exact prime_oneHundredTwelveDF_25243
      · exact prime_oneHundredTwelveDF_29251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3353735554207) ^ 1676867777103 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 1117911851402 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 4430297958 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 132858042 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 114653706 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3467396948839 : Nat.Prime 3467396948839 := by
  apply lucas_primality 3467396948839 (3 : ZMod 3467396948839)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (149, 1), (353, 1), (100801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (149, 1), (353, 1), (100801, 1)] : List FactorBlock).map factorBlockValue).prod) = 3467396948839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_149
      · exact prime_oneHundredTwelveDF_353
      · exact prime_oneHundredTwelveDF_100801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3467396948839) ^ 1733698474419 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 1155798982946 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 31810981182 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 23271120462 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 9822654246 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 34398438 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4934642467331 : Nat.Prime 4934642467331 := by
  apply lucas_primality 4934642467331 (2 : ZMod 4934642467331)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) = 4934642467331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_25919
      · exact prime_oneHundredTwelveDF_19038707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4934642467331) ^ 2467321233665 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 986928493466 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 190387070 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 259190 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_7147400695349 : Nat.Prime 7147400695349 := by
  apply lucas_primality 7147400695349 (3 : ZMod 7147400695349)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (43581711557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (43581711557, 1)] : List FactorBlock).map factorBlockValue).prod) = 7147400695349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_43581711557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7147400695349) ^ 3573700347674 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7147400695349) ^ 174326846228 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 7147400695349) ^ 164 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_8811217929209 : Nat.Prime 8811217929209 := by
  apply lucas_primality 8811217929209 (3 : ZMod 8811217929209)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1101402241151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1101402241151, 1)] : List FactorBlock).map factorBlockValue).prod) = 8811217929209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1101402241151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 8811217929209) ^ 4405608964604 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8811217929209) ^ 8 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_229
      · exact prime_oneHundredTwelveDF_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10981426522441 : Nat.Prime 10981426522441 := by
  apply lucas_primality 10981426522441 (43 : ZMod 10981426522441)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 10981426522441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_103
      · exact prime_oneHundredTwelveDF_647
      · exact prime_oneHundredTwelveDF_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 10981426522441) ^ 5490713261220 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 3660475507480 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2196285304488 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 998311502040 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 354239565240 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 106615791480 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 16972838520 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2726949720 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_12188654129741 : Nat.Prime 12188654129741 := by
  apply lucas_primality 12188654129741 (2 : ZMod 12188654129741)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (31699, 1), (1747783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (31699, 1), (1747783, 1)] : List FactorBlock).map factorBlockValue).prod) = 12188654129741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_31699
      · exact prime_oneHundredTwelveDF_1747783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12188654129741) ^ 6094327064870 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12188654129741) ^ 2437730825948 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12188654129741) ^ 1108059466340 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12188654129741) ^ 384512260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 12188654129741) ^ 6973780 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_13763311522591 : Nat.Prime 13763311522591 := by
  apply lucas_primality 13763311522591 (6 : ZMod 13763311522591)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (3779, 1), (17343101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (3779, 1), (17343101, 1)] : List FactorBlock).map factorBlockValue).prod) = 13763311522591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_3779
      · exact prime_oneHundredTwelveDF_17343101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13763311522591) ^ 6881655761295 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 4587770507530 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 2752662304518 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 1966187360370 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 3642051210 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 793590 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_14286766865669 : Nat.Prime 14286766865669 := by
  apply lucas_primality 14286766865669 (2 : ZMod 14286766865669)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) = 14286766865669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_324699246947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14286766865669) ^ 7143383432834 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 1298796987788 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 44 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_14294801390699 : Nat.Prime 14294801390699 := by
  apply lucas_primality 14294801390699 (2 : ZMod 14294801390699)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7147400695349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7147400695349, 1)] : List FactorBlock).map factorBlockValue).prod) = 14294801390699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7147400695349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14294801390699) ^ 7147400695349 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14294801390699) ^ 2 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_61
      · exact prime_oneHundredTwelveDF_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_21165541112407 : Nat.Prime 21165541112407 := by
  apply lucas_primality 21165541112407 (3 : ZMod 21165541112407)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (379, 1), (92311, 1), (100829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (379, 1), (92311, 1), (100829, 1)] : List FactorBlock).map factorBlockValue).prod) = 21165541112407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_379
      · exact prime_oneHundredTwelveDF_92311
      · exact prime_oneHundredTwelveDF_100829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21165541112407) ^ 10582770556203 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21165541112407) ^ 7055180370802 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21165541112407) ^ 55845754914 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21165541112407) ^ 229285146 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 21165541112407) ^ 209915214 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_22449387575971 : Nat.Prime 22449387575971 := by
  apply lucas_primality 22449387575971 (2 : ZMod 22449387575971)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (23, 1), (53, 1), (113, 1), (603613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (23, 1), (53, 1), (113, 1), (603613, 1)] : List FactorBlock).map factorBlockValue).prod) = 22449387575971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_53
      · exact prime_oneHundredTwelveDF_113
      · exact prime_oneHundredTwelveDF_603613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22449387575971) ^ 11224693787985 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 7483129191990 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 4489877515194 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 976060329390 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 423573350490 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 198667146690 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 22449387575971) ^ 37191690 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_24251390888827 : Nat.Prime 24251390888827 := by
  apply lucas_primality 24251390888827 (2 : ZMod 24251390888827)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4519, 1), (894423209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4519, 1), (894423209, 1)] : List FactorBlock).map factorBlockValue).prod) = 24251390888827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_4519
      · exact prime_oneHundredTwelveDF_894423209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24251390888827) ^ 12125695444413 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 8083796962942 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 5366539254 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 27114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_30914069692613 : Nat.Prime 30914069692613 := by
  apply lucas_primality 30914069692613 (2 : ZMod 30914069692613)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2113, 1), (32771, 1), (111611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2113, 1), (32771, 1), (111611, 1)] : List FactorBlock).map factorBlockValue).prod) = 30914069692613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_2113
      · exact prime_oneHundredTwelveDF_32771
      · exact prime_oneHundredTwelveDF_111611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30914069692613) ^ 15457034846306 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30914069692613) ^ 14630416324 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30914069692613) ^ 943336172 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30914069692613) ^ 276980492 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_32520964175027 : Nat.Prime 32520964175027 := by
  apply lucas_primality 32520964175027 (2 : ZMod 32520964175027)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32520964175027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_53
      · exact prime_oneHundredTwelveDF_1151
      · exact prime_oneHundredTwelveDF_266552171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32520964175027) ^ 16260482087513 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 613603097642 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 28254530126 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 122006 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_33699022756921 : Nat.Prime 33699022756921 := by
  apply lucas_primality 33699022756921 (13 : ZMod 33699022756921)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) = 33699022756921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_191
      · exact prime_oneHundredTwelveDF_296489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33699022756921) ^ 16849511378460 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 11233007585640 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 6739804551384 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1773632776680 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1162035267480 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 176434674120 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 113660280 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_33980932549547 : Nat.Prime 33980932549547 := by
  apply lucas_primality 33980932549547 (2 : ZMod 33980932549547)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (44171, 1), (384652063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (44171, 1), (384652063, 1)] : List FactorBlock).map factorBlockValue).prod) = 33980932549547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_44171
      · exact prime_oneHundredTwelveDF_384652063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33980932549547) ^ 16990466274773 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33980932549547) ^ 769304126 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 33980932549547) ^ 88342 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_34922139169069 : Nat.Prime 34922139169069 := by
  apply lucas_primality 34922139169069 (2 : ZMod 34922139169069)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (37, 1), (1139905313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (37, 1), (1139905313, 1)] : List FactorBlock).map factorBlockValue).prod) = 34922139169069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_1139905313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34922139169069) ^ 17461069584534 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34922139169069) ^ 11640713056356 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34922139169069) ^ 1518353876916 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34922139169069) ^ 943841599164 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34922139169069) ^ 30636 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_39465167216521 : Nat.Prime 39465167216521 := by
  apply lucas_primality 39465167216521 (13 : ZMod 39465167216521)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (109, 1), (3017214619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (109, 1), (3017214619, 1)] : List FactorBlock).map factorBlockValue).prod) = 39465167216521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_109
      · exact prime_oneHundredTwelveDF_3017214619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 39465167216521) ^ 19732583608260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 39465167216521) ^ 13155055738840 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 39465167216521) ^ 7893033443304 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 39465167216521) ^ 362065754280 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 39465167216521) ^ 13080 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_54647127243493 : Nat.Prime 54647127243493 := by
  apply lucas_primality 54647127243493 (2 : ZMod 54647127243493)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (257, 1), (148903877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (257, 1), (148903877, 1)] : List FactorBlock).map factorBlockValue).prod) = 54647127243493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_257
      · exact prime_oneHundredTwelveDF_148903877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54647127243493) ^ 27323563621746 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 18215709081164 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 7806732463356 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 3214536896676 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 212634736356 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 366996 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_61828139385227 : Nat.Prime 61828139385227 := by
  apply lucas_primality 61828139385227 (2 : ZMod 61828139385227)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30914069692613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30914069692613, 1)] : List FactorBlock).map factorBlockValue).prod) = 61828139385227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_30914069692613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 61828139385227) ^ 30914069692613 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 61828139385227) ^ 2 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_71035660920271 : Nat.Prime 71035660920271 := by
  apply lucas_primality 71035660920271 (6 : ZMod 71035660920271)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (42397, 1), (55849597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (42397, 1), (55849597, 1)] : List FactorBlock).map factorBlockValue).prod) = 71035660920271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_42397
      · exact prime_oneHundredTwelveDF_55849597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 71035660920271) ^ 35517830460135 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 71035660920271) ^ 23678553640090 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 71035660920271) ^ 14207132184054 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 71035660920271) ^ 1675487910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 71035660920271) ^ 1271910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_73131924778447 : Nat.Prime 73131924778447 := by
  apply lucas_primality 73131924778447 (3 : ZMod 73131924778447)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12188654129741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12188654129741, 1)] : List FactorBlock).map factorBlockValue).prod) = 73131924778447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_12188654129741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 73131924778447) ^ 36565962389223 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73131924778447) ^ 24377308259482 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73131924778447) ^ 6 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_89805581217161 : Nat.Prime 89805581217161 := by
  apply lucas_primality 89805581217161 (3 : ZMod 89805581217161)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2245139530429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2245139530429, 1)] : List FactorBlock).map factorBlockValue).prod) = 89805581217161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_2245139530429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 89805581217161) ^ 44902790608580 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 89805581217161) ^ 17961116243432 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 89805581217161) ^ 40 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_115028789035553 : Nat.Prime 115028789035553 := by
  apply lucas_primality 115028789035553 (3 : ZMod 115028789035553)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (59, 1), (1243393171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (59, 1), (1243393171, 1)] : List FactorBlock).map factorBlockValue).prod) = 115028789035553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_59
      · exact prime_oneHundredTwelveDF_1243393171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115028789035553) ^ 57514394517776 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 115028789035553) ^ 16432684147936 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 115028789035553) ^ 1949640492128 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 115028789035553) ^ 92512 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_178957470887677 : Nat.Prime 178957470887677 := by
  apply lucas_primality 178957470887677 (5 : ZMod 178957470887677)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (23, 1), (22787, 1), (729607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (23, 1), (22787, 1), (729607, 1)] : List FactorBlock).map factorBlockValue).prod) = 178957470887677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_22787
      · exact prime_oneHundredTwelveDF_729607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 178957470887677) ^ 89478735443838 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 178957470887677) ^ 59652490295892 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 178957470887677) ^ 13765959299052 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 178957470887677) ^ 7780759603812 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 178957470887677) ^ 7853489748 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 178957470887677) ^ 245279268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_180734914054787 : Nat.Prime 180734914054787 := by
  apply lucas_primality 180734914054787 (2 : ZMod 180734914054787)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (993048978323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (993048978323, 1)] : List FactorBlock).map factorBlockValue).prod) = 180734914054787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_993048978323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 180734914054787) ^ 90367457027393 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 180734914054787) ^ 25819273436398 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 180734914054787) ^ 13902685696522 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 180734914054787) ^ 182 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_199204501037701 : Nat.Prime 199204501037701 := by
  apply lucas_primality 199204501037701 (2 : ZMod 199204501037701)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (47, 1), (4943, 1), (2858179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (47, 1), (4943, 1), (2858179, 1)] : List FactorBlock).map factorBlockValue).prod) = 199204501037701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_4943
      · exact prime_oneHundredTwelveDF_2858179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 199204501037701) ^ 99602250518850 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 199204501037701) ^ 66401500345900 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 199204501037701) ^ 39840900207540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 199204501037701) ^ 4238393639100 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 199204501037701) ^ 40300323900 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 199204501037701) ^ 69696300 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_222070223812357 : Nat.Prime 222070223812357 := by
  apply lucas_primality 222070223812357 (6 : ZMod 222070223812357)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 2), (7334860081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 2), (7334860081, 1)] : List FactorBlock).map factorBlockValue).prod) = 222070223812357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_7334860081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 222070223812357) ^ 111035111906178 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 222070223812357) ^ 74023407937452 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 222070223812357) ^ 7657593924564 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 222070223812357) ^ 30276 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_10789
      · exact prime_oneHundredTwelveDF_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_334826281309943 : Nat.Prime 334826281309943 := by
  apply lucas_primality 334826281309943 (5 : ZMod 334826281309943)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (8811217929209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (8811217929209, 1)] : List FactorBlock).map factorBlockValue).prod) = 334826281309943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_8811217929209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 334826281309943) ^ 167413140654971 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 334826281309943) ^ 17622435858418 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 334826281309943) ^ 38 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_334989034308223 : Nat.Prime 334989034308223 := by
  apply lucas_primality 334989034308223 (3 : ZMod 334989034308223)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) = 334989034308223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_37
      · exact prime_oneHundredTwelveDF_215565659143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334989034308223) ^ 167494517154111 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 111663011436074 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 47855576329746 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 9053757684006 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 1554 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_596270354243449 : Nat.Prime 596270354243449 := by
  apply lucas_primality 596270354243449 (13 : ZMod 596270354243449)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1454081, 1), (17086117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1454081, 1), (17086117, 1)] : List FactorBlock).map factorBlockValue).prod) = 596270354243449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_1454081
      · exact prime_oneHundredTwelveDF_17086117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 596270354243449) ^ 298135177121724 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 596270354243449) ^ 198756784747816 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 596270354243449) ^ 410066808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 596270354243449) ^ 34897944 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_701
      · exact prime_oneHundredTwelveDF_9769
      · exact prime_oneHundredTwelveDF_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_808418374374301 : Nat.Prime 808418374374301 := by
  apply lucas_primality 808418374374301 (6 : ZMod 808418374374301)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) = 808418374374301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_272809
      · exact prime_oneHundredTwelveDF_9877709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 808418374374301) ^ 404209187187150 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 269472791458100 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 161683674874860 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 2963312700 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 81842700 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_910008911973521 : Nat.Prime 910008911973521 := by
  apply lucas_primality 910008911973521 (3 : ZMod 910008911973521)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (5843, 1), (1946792983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (5843, 1), (1946792983, 1)] : List FactorBlock).map factorBlockValue).prod) = 910008911973521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_5843
      · exact prime_oneHundredTwelveDF_1946792983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910008911973521) ^ 455004455986760 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 182001782394704 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 155743438640 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 467440 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1458405570906899 : Nat.Prime 1458405570906899 := by
  apply lucas_primality 1458405570906899 (2 : ZMod 1458405570906899)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (1129, 1), (1193, 1), (1508063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (1129, 1), (1193, 1), (1508063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1458405570906899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_359
      · exact prime_oneHundredTwelveDF_1129
      · exact prime_oneHundredTwelveDF_1193
      · exact prime_oneHundredTwelveDF_1508063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1458405570906899) ^ 729202785453449 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 4062411061022 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 1291767556162 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 1222469045186 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 967072046 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2213500557195517 : Nat.Prime 2213500557195517 := by
  apply lucas_primality 2213500557195517 (2 : ZMod 2213500557195517)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2237, 1), (4850466217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2237, 1), (4850466217, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213500557195517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_2237
      · exact prime_oneHundredTwelveDF_4850466217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2213500557195517) ^ 1106750278597758 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213500557195517) ^ 737833519065172 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213500557195517) ^ 130205915129148 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213500557195517) ^ 989495108268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213500557195517) ^ 456348 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2585614343664029 : Nat.Prime 2585614343664029 := by
  apply lucas_primality 2585614343664029 (2 : ZMod 2585614343664029)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (3281236476731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (3281236476731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2585614343664029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_197
      · exact prime_oneHundredTwelveDF_3281236476731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2585614343664029) ^ 1292807171832014 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585614343664029) ^ 13124945906924 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585614343664029) ^ 788 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3063501856192073 : Nat.Prime 3063501856192073 := by
  apply lucas_primality 3063501856192073 (3 : ZMod 3063501856192073)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (562273, 1), (681053033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (562273, 1), (681053033, 1)] : List FactorBlock).map factorBlockValue).prod) = 3063501856192073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_562273
      · exact prime_oneHundredTwelveDF_681053033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3063501856192073) ^ 1531750928096036 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3063501856192073) ^ 5448424264 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3063501856192073) ^ 4498184 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3432296688844733 : Nat.Prime 3432296688844733 := by
  apply lucas_primality 3432296688844733 (2 : ZMod 3432296688844733)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (1303, 1), (14011433063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (1303, 1), (14011433063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3432296688844733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_47
      · exact prime_oneHundredTwelveDF_1303
      · exact prime_oneHundredTwelveDF_14011433063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3432296688844733) ^ 1716148344422366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432296688844733) ^ 73027589124356 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432296688844733) ^ 2634149415844 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3432296688844733) ^ 244964 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3563453043581677 : Nat.Prime 3563453043581677 := by
  apply lucas_primality 3563453043581677 (5 : ZMod 3563453043581677)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (4241, 1), (80279, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (4241, 1), (80279, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3563453043581677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_4241
      · exact prime_oneHundredTwelveDF_80279
      · exact prime_oneHundredTwelveDF_124601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3563453043581677) ^ 1781726521790838 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 1187817681193892 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 509064720511668 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 840238869036 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 44388358644 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 28598912076 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4490118111021163 : Nat.Prime 4490118111021163 := by
  apply lucas_primality 4490118111021163 (2 : ZMod 4490118111021163)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (1259, 1), (4276278527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (1259, 1), (4276278527, 1)] : List FactorBlock).map factorBlockValue).prod) = 4490118111021163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_139
      · exact prime_oneHundredTwelveDF_1259
      · exact prime_oneHundredTwelveDF_4276278527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4490118111021163) ^ 2245059055510581 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 1496706037007054 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 32303007992958 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 3566416291518 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 1050006 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_7381174988471483 : Nat.Prime 7381174988471483 := by
  apply lucas_primality 7381174988471483 (5 : ZMod 7381174988471483)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (41, 1), (99839, 1), (4313851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (41, 1), (99839, 1), (4313851, 1)] : List FactorBlock).map factorBlockValue).prod) = 7381174988471483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_99839
      · exact prime_oneHundredTwelveDF_4313851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7381174988471483) ^ 3690587494235741 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 7381174988471483) ^ 671015908042862 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 7381174988471483) ^ 388482894130078 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 7381174988471483) ^ 180028658255402 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 7381174988471483) ^ 73930778438 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 7381174988471483) ^ 1711040782 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_8648524669571609 : Nat.Prime 8648524669571609 := by
  apply lucas_primality 8648524669571609 (3 : ZMod 8648524669571609)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (242989, 1), (4449030959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (242989, 1), (4449030959, 1)] : List FactorBlock).map factorBlockValue).prod) = 8648524669571609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_242989
      · exact prime_oneHundredTwelveDF_4449030959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8648524669571609) ^ 4324262334785804 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8648524669571609) ^ 35592247672 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 8648524669571609) ^ 1943912 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10402226321133749 : Nat.Prime 10402226321133749 := by
  apply lucas_primality 10402226321133749 (2 : ZMod 10402226321133749)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) = 10402226321133749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_4934642467331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10402226321133749) ^ 5201113160566874 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 611895665949044 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 335555687778508 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 2108 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_16695774487261171 : Nat.Prime 16695774487261171 := by
  apply lucas_primality 16695774487261171 (3 : ZMod 16695774487261171)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16695774487261171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_97
      · exact prime_oneHundredTwelveDF_167
      · exact prime_oneHundredTwelveDF_545326447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16695774487261171) ^ 8347887243630585 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 5565258162420390 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 3339154897452234 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 2385110641037310 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 172121386466610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 99974697528510 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 30616110 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_18379229417192999 : Nat.Prime 18379229417192999 := by
  apply lucas_primality 18379229417192999 (11 : ZMod 18379229417192999)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) = 18379229417192999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_197
      · exact prime_oneHundredTwelveDF_27799
      · exact prime_oneHundredTwelveDF_1678038433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 18379229417192999) ^ 9189614708596499 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 93295580797934 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 661147142602 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 10952806 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_20162724211452103 : Nat.Prime 20162724211452103 := by
  apply lucas_primality 20162724211452103 (5 : ZMod 20162724211452103)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (29, 1), (871261092881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (29, 1), (871261092881, 1)] : List FactorBlock).map factorBlockValue).prod) = 20162724211452103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_871261092881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20162724211452103) ^ 10081362105726051 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20162724211452103) ^ 6720908070484034 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20162724211452103) ^ 2880389173064586 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20162724211452103) ^ 1061196011129058 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20162724211452103) ^ 695266352119038 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 20162724211452103) ^ 23142 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_131
      · exact prime_oneHundredTwelveDF_170603
      · exact prime_oneHundredTwelveDF_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_145829
      · exact prime_oneHundredTwelveDF_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_55070634248535781 : Nat.Prime 55070634248535781 := by
  apply lucas_primality 55070634248535781 (11 : ZMod 55070634248535781)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (167, 1), (87239226703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (167, 1), (87239226703, 1)] : List FactorBlock).map factorBlockValue).prod) = 55070634248535781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_167
      · exact prime_oneHundredTwelveDF_87239226703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 55070634248535781) ^ 27535317124267890 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 18356878082845260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 11014126849707156 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 7867233464076540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 329764276937340 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 55070634248535781) ^ 631260 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_58162906976894437 : Nat.Prime 58162906976894437 := by
  apply lucas_primality 58162906976894437 (2 : ZMod 58162906976894437)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (21165541112407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (21165541112407, 1)] : List FactorBlock).map factorBlockValue).prod) = 58162906976894437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_229
      · exact prime_oneHundredTwelveDF_21165541112407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58162906976894437) ^ 29081453488447218 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58162906976894437) ^ 19387635658964812 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58162906976894437) ^ 253986493348884 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58162906976894437) ^ 2748 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_24841
      · exact prime_oneHundredTwelveDF_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_70686299745721307 : Nat.Prime 70686299745721307 := by
  apply lucas_primality 70686299745721307 (2 : ZMod 70686299745721307)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1277, 1), (1867, 1), (6691, 1), (2215537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1277, 1), (1867, 1), (6691, 1), (2215537, 1)] : List FactorBlock).map factorBlockValue).prod) = 70686299745721307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1277
      · exact prime_oneHundredTwelveDF_1867
      · exact prime_oneHundredTwelveDF_6691
      · exact prime_oneHundredTwelveDF_2215537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70686299745721307) ^ 35343149872860653 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 70686299745721307) ^ 55353406222178 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 70686299745721307) ^ 37860899703118 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 70686299745721307) ^ 10564384956766 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 70686299745721307) ^ 31904815738 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_80650896845808413 : Nat.Prime 80650896845808413 := by
  apply lucas_primality 80650896845808413 (2 : ZMod 80650896845808413)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20162724211452103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20162724211452103, 1)] : List FactorBlock).map factorBlockValue).prod) = 80650896845808413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_20162724211452103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 80650896845808413) ^ 40325448422904206 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 80650896845808413) ^ 4 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_104997213222150383 : Nat.Prime 104997213222150383 := by
  apply lucas_primality 104997213222150383 (5 : ZMod 104997213222150383)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) = 104997213222150383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_1545121
      · exact prime_oneHundredTwelveDF_4853859953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 104997213222150383) ^ 52498606611075191 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 14999601888878626 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 67954039342 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 21631694 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_174841446850172461 : Nat.Prime 174841446850172461 := by
  apply lucas_primality 174841446850172461 (6 : ZMod 174841446850172461)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (23, 1), (1427, 1), (8599, 1), (1147231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (23, 1), (1427, 1), (8599, 1), (1147231, 1)] : List FactorBlock).map factorBlockValue).prod) = 174841446850172461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_1427
      · exact prime_oneHundredTwelveDF_8599
      · exact prime_oneHundredTwelveDF_1147231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 174841446850172461) ^ 87420723425086230 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 58280482283390820 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 34968289370034492 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 7601802036964020 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 122523788962980 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 20332765071540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 174841446850172461) ^ 152403000660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_182805221679518773 : Nat.Prime 182805221679518773 := by
  apply lucas_primality 182805221679518773 (2 : ZMod 182805221679518773)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (33023, 1), (48491, 1), (3171089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (33023, 1), (48491, 1), (3171089, 1)] : List FactorBlock).map factorBlockValue).prod) = 182805221679518773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_33023
      · exact prime_oneHundredTwelveDF_48491
      · exact prime_oneHundredTwelveDF_3171089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 182805221679518773) ^ 91402610839759386 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 60935073893172924 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 5535693961164 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 3769879393692 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 57647458548 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_232144539887445629 : Nat.Prime 232144539887445629 := by
  apply lucas_primality 232144539887445629 (2 : ZMod 232144539887445629)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (43, 1), (71035660920271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (43, 1), (71035660920271, 1)] : List FactorBlock).map factorBlockValue).prod) = 232144539887445629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_71035660920271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 232144539887445629) ^ 116072269943722814 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 232144539887445629) ^ 12218133678286612 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 232144539887445629) ^ 5398710229940596 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 232144539887445629) ^ 3268 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_336942068690028377 : Nat.Prime 336942068690028377 := by
  apply lucas_primality 336942068690028377 (3 : ZMod 336942068690028377)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (509, 1), (6841, 1), (711506639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (509, 1), (6841, 1), (711506639, 1)] : List FactorBlock).map factorBlockValue).prod) = 336942068690028377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_509
      · exact prime_oneHundredTwelveDF_6841
      · exact prime_oneHundredTwelveDF_711506639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 336942068690028377) ^ 168471034345014188 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336942068690028377) ^ 19820121687648728 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336942068690028377) ^ 661968700766264 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336942068690028377) ^ 49253335578136 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 336942068690028377) ^ 473561384 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_338234065908919183 : Nat.Prime 338234065908919183 := by
  apply lucas_primality 338234065908919183 (5 : ZMod 338234065908919183)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1429, 1), (162971, 1), (26895587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1429, 1), (162971, 1), (26895587, 1)] : List FactorBlock).map factorBlockValue).prod) = 338234065908919183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_1429
      · exact prime_oneHundredTwelveDF_162971
      · exact prime_oneHundredTwelveDF_26895587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 338234065908919183) ^ 169117032954459591 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 112744688636306394 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 236692838284758 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 2075424866442 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 12575820186 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_455574172673841433 : Nat.Prime 455574172673841433 := by
  apply lucas_primality 455574172673841433 (17 : ZMod 455574172673841433)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (83, 1), (8537, 1), (26789492083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (83, 1), (8537, 1), (26789492083, 1)] : List FactorBlock).map factorBlockValue).prod) = 455574172673841433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_83
      · exact prime_oneHundredTwelveDF_8537
      · exact prime_oneHundredTwelveDF_26789492083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 455574172673841433) ^ 227787086336920716 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 455574172673841433) ^ 151858057557947144 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 455574172673841433) ^ 5488845453901704 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 455574172673841433) ^ 53364668229336 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 455574172673841433) ^ 17005704 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_543148124219102323 : Nat.Prime 543148124219102323 := by
  apply lucas_primality 543148124219102323 (2 : ZMod 543148124219102323)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (435881, 1), (23075790403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (435881, 1), (23075790403, 1)] : List FactorBlock).map factorBlockValue).prod) = 543148124219102323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_435881
      · exact prime_oneHundredTwelveDF_23075790403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 543148124219102323) ^ 271574062109551161 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 543148124219102323) ^ 181049374739700774 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 543148124219102323) ^ 1246092681762 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 543148124219102323) ^ 23537574 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_544488984971724911 : Nat.Prime 544488984971724911 := by
  apply lucas_primality 544488984971724911 (43 : ZMod 544488984971724911)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (293, 1), (14294801390699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (293, 1), (14294801390699, 1)] : List FactorBlock).map factorBlockValue).prod) = 544488984971724911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_293
      · exact prime_oneHundredTwelveDF_14294801390699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 544488984971724911) ^ 272244492485862455 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 544488984971724911) ^ 108897796994344982 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 544488984971724911) ^ 41883768074748070 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 544488984971724911) ^ 1858324180790870 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (43 : ZMod 544488984971724911) ^ 38090 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_667182991965369403 : Nat.Prime 667182991965369403 := by
  apply lucas_primality 667182991965369403 (2 : ZMod 667182991965369403)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (131, 1), (389, 1), (839, 1), (49072139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (131, 1), (389, 1), (839, 1), (49072139, 1)] : List FactorBlock).map factorBlockValue).prod) = 667182991965369403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_53
      · exact prime_oneHundredTwelveDF_131
      · exact prime_oneHundredTwelveDF_389
      · exact prime_oneHundredTwelveDF_839
      · exact prime_oneHundredTwelveDF_49072139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 667182991965369403) ^ 333591495982684701 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 222394330655123134 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 12588358338969234 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 5092999938666942 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 1715123372661618 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 795212147753718 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 667182991965369403) ^ 13595963118 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_878478886576156007 : Nat.Prime 878478886576156007 := by
  apply lucas_primality 878478886576156007 (5 : ZMod 878478886576156007)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (967, 1), (3467396948839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (967, 1), (3467396948839, 1)] : List FactorBlock).map factorBlockValue).prod) = 878478886576156007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_131
      · exact prime_oneHundredTwelveDF_967
      · exact prime_oneHundredTwelveDF_3467396948839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 878478886576156007) ^ 439239443288078003 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 6705945699054626 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 908458000595818 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 253354 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1427869039791532991 : Nat.Prime 1427869039791532991 := by
  apply lucas_primality 1427869039791532991 (7 : ZMod 1427869039791532991)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (19, 1), (224221, 1), (1971558053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (19, 1), (224221, 1), (1971558053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427869039791532991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_224221
      · exact prime_oneHundredTwelveDF_1971558053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1427869039791532991) ^ 713934519895766495 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427869039791532991) ^ 285573807958306598 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427869039791532991) ^ 83992296458325470 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427869039791532991) ^ 75151002094291210 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427869039791532991) ^ 6368132511190 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427869039791532991) ^ 724233830 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1541977758959001869 : Nat.Prime 1541977758959001869 := by
  apply lucas_primality 1541977758959001869 (2 : ZMod 1541977758959001869)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (55070634248535781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (55070634248535781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1541977758959001869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_55070634248535781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1541977758959001869) ^ 770988879479500934 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541977758959001869) ^ 220282536994143124 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1541977758959001869) ^ 28 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2068648210956352507 : Nat.Prime 2068648210956352507 := by
  apply lucas_primality 2068648210956352507 (2 : ZMod 2068648210956352507)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2068648210956352507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_787
      · exact prime_oneHundredTwelveDF_33699022756921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2068648210956352507) ^ 1034324105478176253 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 689549403652117502 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 159126785458180962 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 2628523775039838 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 61386 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_101
      · exact prime_oneHundredTwelveDF_191
      · exact prime_oneHundredTwelveDF_48017
      · exact prime_oneHundredTwelveDF_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3765515772023157961 : Nat.Prime 3765515772023157961 := by
  apply lucas_primality 3765515772023157961 (17 : ZMod 3765515772023157961)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (8734511, 1), (1197521651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (8734511, 1), (1197521651, 1)] : List FactorBlock).map factorBlockValue).prod) = 3765515772023157961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_8734511
      · exact prime_oneHundredTwelveDF_1197521651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3765515772023157961) ^ 1882757886011578980 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 3765515772023157961) ^ 1255171924007719320 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 3765515772023157961) ^ 753103154404631592 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 3765515772023157961) ^ 431107794360 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 3765515772023157961) ^ 3144423960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_3873419681044591673 : Nat.Prime 3873419681044591673 := by
  apply lucas_primality 3873419681044591673 (3 : ZMod 3873419681044591673)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873419681044591673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_29
      · exact prime_oneHundredTwelveDF_16695774487261171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3873419681044591673) ^ 1936709840522295836 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 133566195898089368 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 232 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4873991417970856459 : Nat.Prime 4873991417970856459 := by
  apply lucas_primality 4873991417970856459 (2 : ZMod 4873991417970856459)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (557, 1), (1458405570906899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (557, 1), (1458405570906899, 1)] : List FactorBlock).map factorBlockValue).prod) = 4873991417970856459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_557
      · exact prime_oneHundredTwelveDF_1458405570906899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4873991417970856459) ^ 2436995708985428229 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 1624663805990285486 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 8750433425441394 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 3342 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10006176146377349017 : Nat.Prime 10006176146377349017 := by
  apply lucas_primality 10006176146377349017 (10 : ZMod 10006176146377349017)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (3563453043581677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (3563453043581677, 1)] : List FactorBlock).map factorBlockValue).prod) = 10006176146377349017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_3563453043581677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 10006176146377349017) ^ 5003088073188674508 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 3335392048792449672 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 769705857413642232 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 2808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_18217245554191692889 : Nat.Prime 18217245554191692889 := by
  apply lucas_primality 18217245554191692889 (7 : ZMod 18217245554191692889)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (97, 1), (101, 1), (131, 1), (1429, 1), (3420499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (97, 1), (101, 1), (131, 1), (1429, 1), (3420499, 1)] : List FactorBlock).map factorBlockValue).prod) = 18217245554191692889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_97
      · exact prime_oneHundredTwelveDF_101
      · exact prime_oneHundredTwelveDF_131
      · exact prime_oneHundredTwelveDF_1429
      · exact prime_oneHundredTwelveDF_3420499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18217245554191692889) ^ 9108622777095846444 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 6072415184730564296 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 1656113232199244808 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 187806655197852504 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 180368767863284088 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 139062943161768648 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 12748247413710072 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 18217245554191692889) ^ 5325902903112 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_53304800954231402413 : Nat.Prime 53304800954231402413 := by
  apply lucas_primality 53304800954231402413 (2 : ZMod 53304800954231402413)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 2), (73, 1), (115028789035553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 2), (73, 1), (115028789035553, 1)] : List FactorBlock).map factorBlockValue).prod) = 53304800954231402413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_73
      · exact prime_oneHundredTwelveDF_115028789035553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53304800954231402413) ^ 26652400477115701206 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53304800954231402413) ^ 17768266984743800804 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53304800954231402413) ^ 2317600041488321844 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53304800954231402413) ^ 730202752797690444 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 53304800954231402413) ^ 463404 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_66344737026778446149 : Nat.Prime 66344737026778446149 := by
  apply lucas_primality 66344737026778446149 (3 : ZMod 66344737026778446149)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) = 66344737026778446149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_319053557
      · exact prime_oneHundredTwelveDF_4725961831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66344737026778446149) ^ 33172368513389223074 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 6031339729707131468 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 207942320564 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 14038356508 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_85554133689319977371 : Nat.Prime 85554133689319977371 := by
  apply lucas_primality 85554133689319977371 (2 : ZMod 85554133689319977371)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (107, 1), (181, 1), (33980932549547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (107, 1), (181, 1), (33980932549547, 1)] : List FactorBlock).map factorBlockValue).prod) = 85554133689319977371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_107
      · exact prime_oneHundredTwelveDF_181
      · exact prime_oneHundredTwelveDF_33980932549547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85554133689319977371) ^ 42777066844659988685 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 17110826737863995474 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 6581087206870767490 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 799571342890840910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 472674771764198770 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 2517710 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_94268036096709849533 : Nat.Prime 94268036096709849533 := by
  apply lucas_primality 94268036096709849533 (2 : ZMod 94268036096709849533)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 94268036096709849533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_23
      · exact prime_oneHundredTwelveDF_263
      · exact prime_oneHundredTwelveDF_16339
      · exact prime_oneHundredTwelveDF_14026408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94268036096709849533) ^ 47134018048354924766 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5545178593924108796 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 4098610265074341284 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 358433597325892964 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5769510747090388 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 6720753548 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_134102943338631294047 : Nat.Prime 134102943338631294047 := by
  apply lucas_primality 134102943338631294047 (5 : ZMod 134102943338631294047)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (336942068690028377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (336942068690028377, 1)] : List FactorBlock).map factorBlockValue).prod) = 134102943338631294047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_199
      · exact prime_oneHundredTwelveDF_336942068690028377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 134102943338631294047) ^ 67051471669315647023 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 134102943338631294047) ^ 673884137380056754 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 134102943338631294047) ^ 398 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_73
      · exact prime_oneHundredTwelveDF_79
      · exact prime_oneHundredTwelveDF_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_377942286057032472047 : Nat.Prime 377942286057032472047 := by
  apply lucas_primality 377942286057032472047 (5 : ZMod 377942286057032472047)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) = 377942286057032472047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_113
      · exact prime_oneHundredTwelveDF_199
      · exact prime_oneHundredTwelveDF_1592737
      · exact prime_oneHundredTwelveDF_5276183617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377942286057032472047) ^ 188971143028516236023 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 3344622000504712142 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 1899207467623278754 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 237291081990958 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 71631753838 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_759663836625866376317 : Nat.Prime 759663836625866376317 := by
  apply lucas_primality 759663836625866376317 (2 : ZMod 759663836625866376317)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (1499, 1), (2585614343664029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (1499, 1), (2585614343664029, 1)] : List FactorBlock).map factorBlockValue).prod) = 759663836625866376317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_1499
      · exact prime_oneHundredTwelveDF_2585614343664029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 759663836625866376317) ^ 379831918312933188158 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759663836625866376317) ^ 108523405232266625188 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759663836625866376317) ^ 506780411358149684 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 759663836625866376317) ^ 293804 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_789307671020222056531 : Nat.Prime 789307671020222056531 := by
  apply lucas_primality 789307671020222056531 (2 : ZMod 789307671020222056531)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1171981, 1), (22449387575971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1171981, 1), (22449387575971, 1)] : List FactorBlock).map factorBlockValue).prod) = 789307671020222056531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_1171981
      · exact prime_oneHundredTwelveDF_22449387575971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 789307671020222056531) ^ 394653835510111028265 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 789307671020222056531) ^ 263102557006740685510 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 789307671020222056531) ^ 157861534204044411306 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 789307671020222056531) ^ 673481627279130 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 789307671020222056531) ^ 35159430 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1351712741721838410479 : Nat.Prime 1351712741721838410479 := by
  apply lucas_primality 1351712741721838410479 (11 : ZMod 1351712741721838410479)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1013, 1), (667182991965369403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1013, 1), (667182991965369403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1351712741721838410479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1013
      · exact prime_oneHundredTwelveDF_667182991965369403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1351712741721838410479) ^ 675856370860919205239 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1351712741721838410479) ^ 1334365983930738806 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 1351712741721838410479) ^ 2026 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1543904714455292433221 : Nat.Prime 1543904714455292433221 := by
  apply lucas_primality 1543904714455292433221 (3 : ZMod 1543904714455292433221)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (43, 1), (313, 1), (4421, 1), (41850003229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (43, 1), (313, 1), (4421, 1), (41850003229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1543904714455292433221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_31
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_313
      · exact prime_oneHundredTwelveDF_4421
      · exact prime_oneHundredTwelveDF_41850003229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1543904714455292433221) ^ 771952357227646216610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 308780942891058486644 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 49803377885654594620 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 35904760801285870540 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 4932602921582403940 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 349220699944648820 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1543904714455292433221) ^ 36891388180 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1991875999464718601911 : Nat.Prime 1991875999464718601911 := by
  apply lucas_primality 1991875999464718601911 (3 : ZMod 1991875999464718601911)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (19, 1), (31319, 1), (611953, 1), (825029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (19, 1), (31319, 1), (611953, 1), (825029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1991875999464718601911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_31319
      · exact prime_oneHundredTwelveDF_611953
      · exact prime_oneHundredTwelveDF_825029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1991875999464718601911) ^ 995937999732359300955 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 663958666488239533970 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 398375199892943720382 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 153221230728055277070 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 117169176439101094230 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 104835578919195715890 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 63599604057112890 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 3254949317128470 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1991875999464718601911) ^ 2414310284201790 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_2754025285986984599839 : Nat.Prime 2754025285986984599839 := by
  apply lucas_primality 2754025285986984599839 (6 : ZMod 2754025285986984599839)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (281, 1), (544488984971724911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (281, 1), (544488984971724911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754025285986984599839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_281
      · exact prime_oneHundredTwelveDF_544488984971724911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2754025285986984599839) ^ 1377012642993492299919 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2754025285986984599839) ^ 918008428662328199946 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2754025285986984599839) ^ 9800801729491048398 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 2754025285986984599839) ^ 5058 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_9803875754057824351433 : Nat.Prime 9803875754057824351433 := by
  apply lucas_primality 9803875754057824351433 (3 : ZMod 9803875754057824351433)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9803875754057824351433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_94268036096709849533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9803875754057824351433) ^ 4901937877028912175716 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 754144288773678796264 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 104 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_14172787871626434216079 : Nat.Prime 14172787871626434216079 := by
  apply lucas_primality 14172787871626434216079 (6 : ZMod 14172787871626434216079)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (2971, 1), (17257, 1), (317189, 1), (694979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (2971, 1), (17257, 1), (317189, 1), (694979, 1)] : List FactorBlock).map factorBlockValue).prod) = 14172787871626434216079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_19
      · exact prime_oneHundredTwelveDF_2971
      · exact prime_oneHundredTwelveDF_17257
      · exact prime_oneHundredTwelveDF_317189
      · exact prime_oneHundredTwelveDF_694979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14172787871626434216079) ^ 7086393935813217108039 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 4724262623875478072026 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 1288435261056948565098 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 745936203769812327162 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 4770376261065780618 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 821277619031490654 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 44682469668325302 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 20393116729608282 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_27718496496200329254761 : Nat.Prime 27718496496200329254761 := by
  apply lucas_primality 27718496496200329254761 (3 : ZMod 27718496496200329254761)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (53304800954231402413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (53304800954231402413, 1)] : List FactorBlock).map factorBlockValue).prod) = 27718496496200329254761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_53304800954231402413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27718496496200329254761) ^ 13859248248100164627380 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27718496496200329254761) ^ 5543699299240065850952 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27718496496200329254761) ^ 2132192038169256096520 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 27718496496200329254761) ^ 520 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_45326794848457377387887 : Nat.Prime 45326794848457377387887 := by
  apply lucas_primality 45326794848457377387887 (5 : ZMod 45326794848457377387887)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (134102943338631294047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (134102943338631294047, 1)] : List FactorBlock).map factorBlockValue).prod) = 45326794848457377387887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_13
      · exact prime_oneHundredTwelveDF_134102943338631294047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45326794848457377387887) ^ 22663397424228688693943 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45326794848457377387887) ^ 3486676526804413645222 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 45326794848457377387887) ^ 338 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_94954930555009359595661 : Nat.Prime 94954930555009359595661 := by
  apply lucas_primality 94954930555009359595661 (2 : ZMod 94954930555009359595661)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) = 94954930555009359595661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_1621
      · exact prime_oneHundredTwelveDF_3623
      · exact prime_oneHundredTwelveDF_808418374374301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94954930555009359595661) ^ 47477465277504679797830 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 18990986111001871919132 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 58577995407161850460 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 26208923697214838420 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 117457660 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_97955932606520422765169 : Nat.Prime 97955932606520422765169 := by
  apply lucas_primality 97955932606520422765169 (3 : ZMod 97955932606520422765169)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (16063, 1), (14017337, 1), (27190587233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (16063, 1), (14017337, 1), (27190587233, 1)] : List FactorBlock).map factorBlockValue).prod) = 97955932606520422765169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_16063
      · exact prime_oneHundredTwelveDF_14017337
      · exact prime_oneHundredTwelveDF_27190587233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 97955932606520422765169) ^ 48977966303260211382584 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 97955932606520422765169) ^ 6098233991565736336 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 97955932606520422765169) ^ 6988198443578864 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 97955932606520422765169) ^ 3602567747696 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_152115249699610919765639 : Nat.Prime 152115249699610919765639 := by
  apply lucas_primality 152115249699610919765639 (7 : ZMod 152115249699610919765639)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (127, 1), (85554133689319977371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (127, 1), (85554133689319977371, 1)] : List FactorBlock).map factorBlockValue).prod) = 152115249699610919765639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_127
      · exact prime_oneHundredTwelveDF_85554133689319977371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 152115249699610919765639) ^ 76057624849805459882819 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 21730749957087274252234 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 1197757871650479683194 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 1778 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_363690497301491172040717 : Nat.Prime 363690497301491172040717 := by
  apply lucas_primality 363690497301491172040717 (2 : ZMod 363690497301491172040717)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) = 363690497301491172040717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_157
      · exact prime_oneHundredTwelveDF_13511921
      · exact prime_oneHundredTwelveDF_14286766865669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 363690497301491172040717) ^ 181845248650745586020358 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 121230165767163724013572 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 2316499982812045681788 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 26916268774920396 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 25456459164 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_535327898490469461943847 : Nat.Prime 535327898490469461943847 := by
  apply lucas_primality 535327898490469461943847 (5 : ZMod 535327898490469461943847)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83933, 1), (455574172673841433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83933, 1), (455574172673841433, 1)] : List FactorBlock).map factorBlockValue).prod) = 535327898490469461943847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_83933
      · exact prime_oneHundredTwelveDF_455574172673841433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 535327898490469461943847) ^ 267663949245234730971923 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 535327898490469461943847) ^ 76475414070067065991978 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 535327898490469461943847) ^ 6378038417433780062 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 535327898490469461943847) ^ 1175062 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1242914450833210793460107 : Nat.Prime 1242914450833210793460107 := by
  apply lucas_primality 1242914450833210793460107 (2 : ZMod 1242914450833210793460107)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (248483, 1), (58162906976894437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (248483, 1), (58162906976894437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1242914450833210793460107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_248483
      · exact prime_oneHundredTwelveDF_58162906976894437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1242914450833210793460107) ^ 621457225416605396730053 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1242914450833210793460107) ^ 28904987228679320778142 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1242914450833210793460107) ^ 5002010000012921582 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1242914450833210793460107) ^ 21369538 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1410068483584820052832327 : Nat.Prime 1410068483584820052832327 := by
  apply lucas_primality 1410068483584820052832327 (3 : ZMod 1410068483584820052832327)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (11717, 1), (4562083, 1), (8126659771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (11717, 1), (4562083, 1), (8126659771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1410068483584820052832327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_541
      · exact prime_oneHundredTwelveDF_11717
      · exact prime_oneHundredTwelveDF_4562083
      · exact prime_oneHundredTwelveDF_8126659771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1410068483584820052832327) ^ 705034241792410026416163 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 470022827861606684277442 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 2606411245073604533886 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 120343815275652475278 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 309084355454475522 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 173511445454706 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_1454761989205964688162869 : Nat.Prime 1454761989205964688162869 := by
  apply lucas_primality 1454761989205964688162869 (2 : ZMod 1454761989205964688162869)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454761989205964688162869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_363690497301491172040717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1454761989205964688162869) ^ 727380994602982344081434 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454761989205964688162869) ^ 4 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_97
      · exact prime_oneHundredTwelveDF_719
      · exact prime_oneHundredTwelveDF_17207
      · exact prime_oneHundredTwelveDF_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_7840244598230570897108917 : Nat.Prime 7840244598230570897108917 := by
  apply lucas_primality 7840244598230570897108917 (2 : ZMod 7840244598230570897108917)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (659, 1), (44773, 1), (7381174988471483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (659, 1), (44773, 1), (7381174988471483, 1)] : List FactorBlock).map factorBlockValue).prod) = 7840244598230570897108917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_659
      · exact prime_oneHundredTwelveDF_44773
      · exact prime_oneHundredTwelveDF_7381174988471483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7840244598230570897108917) ^ 3920122299115285448554458 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840244598230570897108917) ^ 2613414866076856965702972 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840244598230570897108917) ^ 11897184519318013500924 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840244598230570897108917) ^ 175110995426497462692 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840244598230570897108917) ^ 1062194652 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_10954160408629724675816719 : Nat.Prime 10954160408629724675816719 := by
  apply lucas_primality 10954160408629724675816719 (3 : ZMod 10954160408629724675816719)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) = 10954160408629724675816719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_17
      · exact prime_oneHundredTwelveDF_16787
      · exact prime_oneHundredTwelveDF_857453
      · exact prime_oneHundredTwelveDF_2486991238073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10954160408629724675816719) ^ 5477080204314862337908359 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 3651386802876574891938906 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 644362376978219098577454 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 652538298006178869114 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 12775231305540624006 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 4404583434366 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_16083309974434120233362383 : Nat.Prime 16083309974434120233362383 := by
  apply lucas_primality 16083309974434120233362383 (6 : ZMod 16083309974434120233362383)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (273549391187, 1), (890831866621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (273549391187, 1), (890831866621, 1)] : List FactorBlock).map factorBlockValue).prod) = 16083309974434120233362383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_11
      · exact prime_oneHundredTwelveDF_273549391187
      · exact prime_oneHundredTwelveDF_890831866621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16083309974434120233362383) ^ 8041654987217060116681191 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 16083309974434120233362383) ^ 5361103324811373411120794 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 16083309974434120233362383) ^ 1462119088584920021214762 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 16083309974434120233362383) ^ 58794903196986 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (6 : ZMod 16083309974434120233362383) ^ 18054259818342 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_21264475834192405954917697 : Nat.Prime 21264475834192405954917697 := by
  apply lucas_primality 21264475834192405954917697 (5 : ZMod 21264475834192405954917697)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1791295669, 1), (61828139385227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1791295669, 1), (61828139385227, 1)] : List FactorBlock).map factorBlockValue).prod) = 21264475834192405954917697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_1791295669
      · exact prime_oneHundredTwelveDF_61828139385227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21264475834192405954917697) ^ 10632237917096202977458848 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21264475834192405954917697) ^ 7088158611397468651639232 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21264475834192405954917697) ^ 11871002761963584 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21264475834192405954917697) ^ 343928768448 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_409950126995405919137066561 : Nat.Prime 409950126995405919137066561 := by
  apply lucas_primality 409950126995405919137066561 (3 : ZMod 409950126995405919137066561)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (101, 1), (37882631, 1), (334826281309943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (101, 1), (37882631, 1), (334826281309943, 1)] : List FactorBlock).map factorBlockValue).prod) = 409950126995405919137066561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_101
      · exact prime_oneHundredTwelveDF_37882631
      · exact prime_oneHundredTwelveDF_334826281309943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 409950126995405919137066561) ^ 204975063497702959568533280 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 409950126995405919137066561) ^ 81990025399081183827413312 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 409950126995405919137066561) ^ 4058912148469365536010560 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 409950126995405919137066561) ^ 10821585411937357760 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 409950126995405919137066561) ^ 1224366633920 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_843400579742140840008105091 : Nat.Prime 843400579742140840008105091 := by
  apply lucas_primality 843400579742140840008105091 (10 : ZMod 843400579742140840008105091)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (97955932606520422765169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (97955932606520422765169, 1)] : List FactorBlock).map factorBlockValue).prod) = 843400579742140840008105091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_41
      · exact prime_oneHundredTwelveDF_97955932606520422765169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 843400579742140840008105091) ^ 421700289871070420004052545 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 843400579742140840008105091) ^ 281133526580713613336035030 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 843400579742140840008105091) ^ 168680115948428168001621018 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 843400579742140840008105091) ^ 120485797106020120001157870 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 843400579742140840008105091) ^ 20570745847369288780685490 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (10 : ZMod 843400579742140840008105091) ^ 8610 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_4137934094359878496289765603 : Nat.Prime 4137934094359878496289765603 := by
  apply lucas_primality 4137934094359878496289765603 (2 : ZMod 4137934094359878496289765603)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 4137934094359878496289765603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_43
      · exact prime_oneHundredTwelveDF_4282273
      · exact prime_oneHundredTwelveDF_32701811
      · exact prime_oneHundredTwelveDF_343588771969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4137934094359878496289765603) ^ 2068967047179939248144882801 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 96231025450229732471855014 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 966293857108100883874 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 126535319232316476182 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 12043275077490658 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_5296555640780644475250899971 : Nat.Prime 5296555640780644475250899971 := by
  apply lucas_primality 5296555640780644475250899971 (2 : ZMod 5296555640780644475250899971)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (127, 1), (1667, 1), (1951, 1), (4474849, 1), (95520658789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (127, 1), (1667, 1), (1951, 1), (4474849, 1), (95520658789, 1)] : List FactorBlock).map factorBlockValue).prod) = 5296555640780644475250899971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_127
      · exact prime_oneHundredTwelveDF_1667
      · exact prime_oneHundredTwelveDF_1951
      · exact prime_oneHundredTwelveDF_4474849
      · exact prime_oneHundredTwelveDF_95520658789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5296555640780644475250899971) ^ 2648277820390322237625449985 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 1765518546926881491750299990 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 1059311128156128895050179994 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 41705162525831846261818110 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 3177297924883410003149910 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 2714790179795307265633470 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 1183627791860830270530 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5296555640780644475250899971) ^ 55449320680256730 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_12037626456319646534661136297 : Nat.Prime 12037626456319646534661136297 := by
  apply lucas_primality 12037626456319646534661136297 (5 : ZMod 12037626456319646534661136297)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 12037626456319646534661136297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_461
      · exact prime_oneHundredTwelveDF_69997
      · exact prime_oneHundredTwelveDF_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12037626456319646534661136297) ^ 6018813228159823267330568148 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12037626456319646534661136297) ^ 4012542152106548844887045432 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12037626456319646534661136297) ^ 1719660922331378076380162328 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12037626456319646534661136297) ^ 26111987974663007667377736 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12037626456319646534661136297) ^ 171973462524388852874568 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 12037626456319646534661136297) ^ 5421127656 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_13241389101951611188127249921 : Nat.Prime 13241389101951611188127249921 := by
  apply lucas_primality 13241389101951611188127249921 (11 : ZMod 13241389101951611188127249921)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 13241389101951611188127249921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_7
      · exact prime_oneHundredTwelveDF_171401
      · exact prime_oneHundredTwelveDF_714027719
      · exact prime_oneHundredTwelveDF_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13241389101951611188127249921) ^ 6620694550975805594063624960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 2648277820390322237625449984 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 1891627014564515884018178560 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 77253861424096774161920 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 18544642945369479680 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 2193140365952596480 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_22068981836586018646878749879 : Nat.Prime 22068981836586018646878749879 := by
  apply lucas_primality 22068981836586018646878749879 (11 : ZMod 22068981836586018646878749879)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (553601, 1), (1815083779, 1), (10981426522441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (553601, 1), (1815083779, 1), (10981426522441, 1)] : List FactorBlock).map factorBlockValue).prod) = 22068981836586018646878749879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_553601
      · exact prime_oneHundredTwelveDF_1815083779
      · exact prime_oneHundredTwelveDF_10981426522441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 22068981836586018646878749879) ^ 11034490918293009323439374939 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 22068981836586018646878749879) ^ 39864418302326077169078 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 22068981836586018646878749879) ^ 12158657408499720082 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (11 : ZMod 22068981836586018646878749879) ^ 2009664390276358 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_44137963673172037293757499737 : Nat.Prime 44137963673172037293757499737 := by
  apply lucas_primality 44137963673172037293757499737 (5 : ZMod 44137963673172037293757499737)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 44137963673172037293757499737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_158265131
      · exact prime_oneHundredTwelveDF_3873419681044591673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44137963673172037293757499737) ^ 22068981836586018646878749868 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44137963673172037293757499737) ^ 14712654557724012431252499912 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44137963673172037293757499737) ^ 278886217035210600456 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44137963673172037293757499737) ^ 11395089432 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_44137963673172037293757499743 : Nat.Prime 44137963673172037293757499743 := by
  apply lucas_primality 44137963673172037293757499743 (3 : ZMod 44137963673172037293757499743)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (44893, 1), (11905824439, 1), (13763311522591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (44893, 1), (11905824439, 1), (13763311522591, 1)] : List FactorBlock).map factorBlockValue).prod) = 44137963673172037293757499743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_44893
      · exact prime_oneHundredTwelveDF_11905824439
      · exact prime_oneHundredTwelveDF_13763311522591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44137963673172037293757499743) ^ 22068981836586018646878749871 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 44137963673172037293757499743) ^ 14712654557724012431252499914 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 44137963673172037293757499743) ^ 983181424123405370408694 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 44137963673172037293757499743) ^ 3707258065102066578 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 44137963673172037293757499743) ^ 3206929059240162 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_132413891019516111881272499273 : Nat.Prime 132413891019516111881272499273 := by
  apply lucas_primality 132413891019516111881272499273 (3 : ZMod 132413891019516111881272499273)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_1511
      · exact prime_oneHundredTwelveDF_10954160408629724675816719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 132413891019516111881272499273) ^ 66206945509758055940636249636 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 132413891019516111881272499273) ^ 87633283269037797406533752 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (3 : ZMod 132413891019516111881272499273) ^ 12088 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwelveDF_132413891019516111881272499281 : Nat.Prime 132413891019516111881272499281 := by
  apply lucas_primality 132413891019516111881272499281 (17 : ZMod 132413891019516111881272499281)
  · rw [← oneHundredTwelveDFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwelveDF_2
      · exact prime_oneHundredTwelveDF_3
      · exact prime_oneHundredTwelveDF_5
      · exact prime_oneHundredTwelveDF_148193
      · exact prime_oneHundredTwelveDF_732506743
      · exact prime_oneHundredTwelveDF_1694188519151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 132413891019516111881272499281) ^ 66206945509758055940636249640 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 132413891019516111881272499281) ^ 44137963673172037293757499760 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 132413891019516111881272499281) ^ 26482778203903222376254499856 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 132413891019516111881272499281) ^ 893523250217730337338960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 132413891019516111881272499281) ^ 180768153037351782960 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide
    · change (17 : ZMod 132413891019516111881272499281) ^ 78157707671087280 ≠ 1
      rw [← oneHundredTwelveDFFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499200 : Nat.totient 132413891019516111881272499200 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 10), (5, 2), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_171401, prime_oneHundredTwelveDF_714027719, prime_oneHundredTwelveDF_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499201 : Nat.totient 132413891019516111881272499201 = 120147042912037452561641011200 := by
  rw [← show ((([(11, 1), (1039, 1), (1307, 1), (5857, 1), (179099, 1), (789611, 1), (10702079, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_1039, prime_oneHundredTwelveDF_1307, prime_oneHundredTwelveDF_5857, prime_oneHundredTwelveDF_179099, prime_oneHundredTwelveDF_789611, prime_oneHundredTwelveDF_10702079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499202 : Nat.totient 132413891019516111881272499202 = 44137963673170168773151775040 := by
  rw [← show ((([(2, 1), (3, 1), (24251390888827, 1), (910008911973521, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_24251390888827, prime_oneHundredTwelveDF_910008911973521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499203 : Nat.totient 132413891019516111881272499203 = 118065636574676904711475169280 := by
  rw [← show ((([(17, 1), (19, 1), (409950126995405919137066561, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_409950126995405919137066561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499204 : Nat.totient 132413891019516111881272499204 = 65863878864934695397960402944 := by
  rw [← show ((([(2, 2), (193, 1), (2585293, 1), (66344737026778446149, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_193, prime_oneHundredTwelveDF_2585293, prime_oneHundredTwelveDF_66344737026778446149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499205 : Nat.totient 132413891019516111881272499205 = 70297326014521364040789152000 := by
  rw [← show ((([(3, 1), (5, 1), (227, 1), (5711, 1), (9786532061, 1), (695785618691, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_227, prime_oneHundredTwelveDF_5711, prime_oneHundredTwelveDF_9786532061, prime_oneHundredTwelveDF_695785618691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499206 : Nat.totient 132413891019516111881272499206 = 60980347985199163191840980736 := by
  rw [← show ((([(2, 1), (13, 1), (457, 1), (2286437, 1), (4873991417970856459, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_457, prime_oneHundredTwelveDF_2286437, prime_oneHundredTwelveDF_4873991417970856459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499207 : Nat.totient 132413891019516111881272499207 = 109473996102439802018306583168 := by
  rw [← show ((([(7, 1), (29, 1), (997, 1), (1953042799, 1), (334989034308223, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_29, prime_oneHundredTwelveDF_997, prime_oneHundredTwelveDF_1953042799, prime_oneHundredTwelveDF_334989034308223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499208 : Nat.totient 132413891019516111881272499208 = 44137963394285820247151809920 := by
  rw [← show ((([(2, 3), (3, 3), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_158265131, prime_oneHundredTwelveDF_3873419681044591673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499209 : Nat.totient 132413891019516111881272499209 = 126523317075076022421437441280 := by
  rw [← show ((([(23, 1), (1109, 1), (6577, 1), (789307671020222056531, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_23, prime_oneHundredTwelveDF_1109, prime_oneHundredTwelveDF_6577, prime_oneHundredTwelveDF_789307671020222056531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499210 : Nat.totient 132413891019516111881272499210 = 52965556407806444752508999680 := by
  rw [← show ((([(2, 1), (5, 1), (13241389101951611188127249921, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_13241389101951611188127249921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499211 : Nat.totient 132413891019516111881272499211 = 88275927346344074587514999472 := by
  rw [← show ((([(3, 1), (44137963673172037293757499737, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_44137963673172037293757499737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499212 : Nat.totient 132413891019516111881272499212 = 58644165110773780486279616000 := by
  rw [← show ((([(2, 2), (11, 1), (41, 1), (773, 1), (94954930555009359595661, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_41, prime_oneHundredTwelveDF_773, prime_oneHundredTwelveDF_94954930555009359595661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499213 : Nat.totient 132413891019516111881272499213 = 132406050774917881310375373408 := by
  rw [← show ((([(16889, 1), (7840244598230570897108917, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_16889, prime_oneHundredTwelveDF_7840244598230570897108917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499214 : Nat.totient 132413891019516111881272499214 = 37299639565599815740485752064 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_89, prime_oneHundredTwelveDF_347, prime_oneHundredTwelveDF_2755243, prime_oneHundredTwelveDF_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499215 : Nat.totient 132413891019516111881272499215 = 103677003213050586080099581824 := by
  rw [← show ((([(5, 1), (47, 1), (405157, 1), (424324643, 1), (3277510442819, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_47, prime_oneHundredTwelveDF_405157, prime_oneHundredTwelveDF_424324643, prime_oneHundredTwelveDF_3277510442819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499216 : Nat.totient 132413891019516111881272499216 = 66206945509332124502815796736 := by
  rw [← show ((([(2, 4), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_155440836073, prime_oneHundredTwelveDF_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499217 : Nat.totient 132413891019516111881272499217 = 88275927337776860286942255480 := by
  rw [← show ((([(3, 2), (10303924343, 1), (1427869039791532991, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_10303924343, prime_oneHundredTwelveDF_1427869039791532991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499218 : Nat.totient 132413891019516111881272499218 = 66183325466670216498540071520 := by
  rw [← show ((([(2, 1), (2803, 1), (5260447481, 1), (4490118111021163, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_2803, prime_oneHundredTwelveDF_5260447481, prime_oneHundredTwelveDF_4490118111021163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499219 : Nat.totient 132413891019516111881272499219 = 121973033384927640557407904256 := by
  rw [← show ((([(13, 1), (479, 1), (21264475834192405954917697, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_479, prime_oneHundredTwelveDF_21264475834192405954917697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499220 : Nat.totient 132413891019516111881272499220 = 33118633738843692939191255040 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (17, 1), (331, 1), (3169, 1), (12409, 1), (29327, 1), (340078141943, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_331, prime_oneHundredTwelveDF_3169, prime_oneHundredTwelveDF_12409, prime_oneHundredTwelveDF_29327, prime_oneHundredTwelveDF_340078141943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499221 : Nat.totient 132413891019516111881272499221 = 109454784962551391219264946720 := by
  rw [← show ((([(7, 1), (43, 2), (79, 1), (1233371, 1), (104997213222150383, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_43, prime_oneHundredTwelveDF_79, prime_oneHundredTwelveDF_1233371, prime_oneHundredTwelveDF_104997213222150383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499222 : Nat.totient 132413891019516111881272499222 = 62720229808877918444156446848 := by
  rw [← show ((([(2, 1), (19, 1), (42943, 1), (92369, 1), (878478886576156007, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_42943, prime_oneHundredTwelveDF_92369, prime_oneHundredTwelveDF_878478886576156007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499223 : Nat.totient 132413891019516111881272499223 = 79945706756328208953390374400 := by
  rw [← show ((([(3, 1), (11, 1), (263, 1), (169887150217, 1), (89805581217161, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_263, prime_oneHundredTwelveDF_169887150217, prime_oneHundredTwelveDF_89805581217161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499224 : Nat.totient 132413891019516111881272499224 = 65218682367177252466866645024 := by
  rw [← show ((([(2, 3), (67, 1), (653647, 1), (377942286057032472047, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_67, prime_oneHundredTwelveDF_653647, prime_oneHundredTwelveDF_377942286057032472047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499225 : Nat.totient 132413891019516111881272499225 = 103066675615822656272302123200 := by
  rw [← show ((([(5, 2), (37, 1), (71867, 1), (1991875999464718601911, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_37, prime_oneHundredTwelveDF_71867, prime_oneHundredTwelveDF_1991875999464718601911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499226 : Nat.totient 132413891019516111881272499226 = 44136980488037531545530135840 := by
  rw [← show ((([(2, 1), (3, 2), (44893, 1), (11905824439, 1), (13763311522591, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_44893, prime_oneHundredTwelveDF_11905824439, prime_oneHundredTwelveDF_13763311522591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499227 : Nat.totient 132413891019516111881272499227 = 132413891018972963513263747056 := by
  rw [← show ((([(243789649849, 1), (543148124219102323, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_243789649849, prime_oneHundredTwelveDF_543148124219102323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499228 : Nat.totient 132413891019516111881272499228 = 56741304949830443959591236480 := by
  rw [← show ((([(2, 2), (7, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_7561, prime_oneHundredTwelveDF_2416168199, prime_oneHundredTwelveDF_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499229 : Nat.totient 132413891019516111881272499229 = 88275927346344074587514999484 := by
  rw [← show ((([(3, 1), (44137963673172037293757499743, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_44137963673172037293757499743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499230 : Nat.totient 132413891019516111881272499230 = 51253077669431834607957907200 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (13147, 1), (3756671, 1), (8648524669571609, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_31, prime_oneHundredTwelveDF_13147, prime_oneHundredTwelveDF_3756671, prime_oneHundredTwelveDF_8648524669571609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499231 : Nat.totient 132413891019516111881272499231 = 131176086092653403691873430488 := by
  rw [← show ((([(107, 1), (449347, 1), (2754025285986984599839, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_107, prime_oneHundredTwelveDF_449347, prime_oneHundredTwelveDF_2754025285986984599839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499232 : Nat.totient 132413891019516111881272499232 = 38971312407081665035290894336 := by
  rw [← show ((([(2, 5), (3, 1), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_23, prime_oneHundredTwelveDF_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499233 : Nat.totient 132413891019516111881272499233 = 131996175827473721443832718720 := by
  rw [← show ((([(317, 1), (22929341, 1), (18217245554191692889, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_317, prime_oneHundredTwelveDF_22929341, prime_oneHundredTwelveDF_18217245554191692889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499234 : Nat.totient 132413891019516111881272499234 = 60008935252071061543304666880 := by
  rw [← show ((([(2, 1), (11, 1), (419, 1), (2143, 1), (8693, 1), (151787, 1), (262519, 1), (19351279, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_419, prime_oneHundredTwelveDF_2143, prime_oneHundredTwelveDF_8693, prime_oneHundredTwelveDF_151787, prime_oneHundredTwelveDF_262519, prime_oneHundredTwelveDF_19351279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499235 : Nat.totient 132413891019516111881272499235 = 60483076038811928640208637952 := by
  rw [← show ((([(3, 4), (5, 1), (7, 2), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_1277, prime_oneHundredTwelveDF_38153, prime_oneHundredTwelveDF_45994279, prime_oneHundredTwelveDF_2977549837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499236 : Nat.totient 132413891019516111881272499236 = 63923947388149385261412920064 := by
  rw [← show ((([(2, 2), (29, 1), (109736033929, 1), (10402226321133749, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_29, prime_oneHundredTwelveDF_109736033929, prime_oneHundredTwelveDF_10402226321133749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499237 : Nat.totient 132413891019516111881272499237 = 123521963928311261517960806400 := by
  rw [← show ((([(17, 1), (113, 1), (346024648097, 1), (199204501037701, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_113, prime_oneHundredTwelveDF_346024648097, prime_oneHundredTwelveDF_199204501037701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499238 : Nat.totient 132413891019516111881272499238 = 44137935938803689733276147968 := by
  rw [← show ((([(2, 1), (3, 1), (1591813, 1), (7076497397, 1), (1959168993193, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_1591813, prime_oneHundredTwelveDF_7076497397, prime_oneHundredTwelveDF_1959168993193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499239 : Nat.totient 132413891019516111881272499239 = 132397807709541677761039128624 := by
  rw [← show ((([(8233, 1), (16083309974434120233362383, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_8233, prime_oneHundredTwelveDF_16083309974434120233362383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499240 : Nat.totient 132413891019516111881272499240 = 51531053307472703893402066944 := by
  rw [← show ((([(2, 3), (5, 1), (59, 2), (97, 1), (9803875754057824351433, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_59, prime_oneHundredTwelveDF_97, prime_oneHundredTwelveDF_9803875754057824351433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499241 : Nat.totient 132413891019516111881272499241 = 83410758273773049790651983360 := by
  rw [← show ((([(3, 1), (19, 1), (389, 1), (29671, 1), (65699, 1), (3063501856192073, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_389, prime_oneHundredTwelveDF_29671, prime_oneHundredTwelveDF_65699, prime_oneHundredTwelveDF_3063501856192073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499242 : Nat.totient 132413891019516111881272499242 = 56673230341708626606805950000 := by
  rw [← show ((([(2, 1), (7, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_751, prime_oneHundredTwelveDF_3594403, prime_oneHundredTwelveDF_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499243 : Nat.totient 132413891019516111881272499243 = 132413887949922237129428507616 := by
  rw [← show ((([(43213957, 1), (32887474027, 1), (93170621837, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_43213957, prime_oneHundredTwelveDF_32887474027, prime_oneHundredTwelveDF_93170621837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499244 : Nat.totient 132413891019516111881272499244 = 41823437823899919655243776000 := by
  rw [← show ((([(2, 2), (3, 2), (53, 1), (61, 1), (137, 1), (151, 1), (233, 1), (70379, 1), (3353735554207, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_53, prime_oneHundredTwelveDF_61, prime_oneHundredTwelveDF_137, prime_oneHundredTwelveDF_151, prime_oneHundredTwelveDF_233, prime_oneHundredTwelveDF_70379, prime_oneHundredTwelveDF_3353735554207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499245 : Nat.totient 132413891019516111881272499245 = 88296642587191294767405930240 := by
  rw [← show ((([(5, 1), (11, 1), (13, 1), (149, 1), (1242914450833210793460107, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_149, prime_oneHundredTwelveDF_1242914450833210793460107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499246 : Nat.totient 132413891019516111881272499246 = 66181120122966788088512262144 := by
  rw [← show ((([(2, 1), (2689, 1), (55343, 1), (8141093, 1), (54647127243493, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_2689, prime_oneHundredTwelveDF_55343, prime_oneHundredTwelveDF_8141093, prime_oneHundredTwelveDF_54647127243493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499247 : Nat.totient 132413891019516111881272499247 = 88228133124445174747914474720 := by
  rw [← show ((([(3, 1), (1847, 1), (326767152461, 1), (73131924778447, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_1847, prime_oneHundredTwelveDF_326767152461, prime_oneHundredTwelveDF_73131924778447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499248 : Nat.totient 132413891019516111881272499248 = 66206943610464788295843111104 := by
  rw [← show ((([(2, 4), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_34858727, prime_oneHundredTwelveDF_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499249 : Nat.totient 132413891019516111881272499249 = 113488892301935717252961658416 := by
  rw [← show ((([(7, 1), (13003, 1), (1454761989205964688162869, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_13003, prime_oneHundredTwelveDF_1454761989205964688162869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499250 : Nat.totient 132413891019516111881272499250 = 34993368181419901205621760000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 3), (127, 1), (1667, 1), (1951, 1), (4474849, 1), (95520658789, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_127, prime_oneHundredTwelveDF_1667, prime_oneHundredTwelveDF_1951, prime_oneHundredTwelveDF_4474849, prime_oneHundredTwelveDF_95520658789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499251 : Nat.totient 132413891019516111881272499251 = 132413890259852275255231817032 := by
  rw [← show ((([(174305903, 1), (759663836625866376317, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_174305903, prime_oneHundredTwelveDF_759663836625866376317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499252 : Nat.totient 132413891019516111881272499252 = 66206945509721293879531931256 := by
  rw [← show ((([(2, 2), (1801134966187, 1), (18379229417192999, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_1801134966187, prime_oneHundredTwelveDF_18379229417192999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499253 : Nat.totient 132413891019516111881272499253 = 84930862818609088398330716160 := by
  rw [← show ((([(3, 2), (41, 1), (73, 1), (6949, 1), (20256349, 1), (34922139169069, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_41, prime_oneHundredTwelveDF_73, prime_oneHundredTwelveDF_6949, prime_oneHundredTwelveDF_20256349, prime_oneHundredTwelveDF_34922139169069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499254 : Nat.totient 132413891019516111881272499254 = 61716255154269605379964615680 := by
  rw [← show ((([(2, 1), (17, 1), (109, 1), (2521, 1), (14172787871626434216079, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_109, prime_oneHundredTwelveDF_2521, prime_oneHundredTwelveDF_14172787871626434216079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499255 : Nat.totient 132413891019516111881272499255 = 100397619094816676746650746880 := by
  rw [← show ((([(5, 1), (23, 1), (199, 1), (241, 1), (339649, 1), (70686299745721307, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_23, prime_oneHundredTwelveDF_199, prime_oneHundredTwelveDF_241, prime_oneHundredTwelveDF_339649, prime_oneHundredTwelveDF_70686299745721307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499256 : Nat.totient 132413891019516111881272499256 = 34318122479790989678203392000 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_461, prime_oneHundredTwelveDF_69997, prime_oneHundredTwelveDF_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499257 : Nat.totient 132413891019516111881272499257 = 131635572093173324781968045760 := by
  rw [← show ((([(197, 1), (1783, 1), (4079, 1), (2017690943, 1), (45804445331, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_197, prime_oneHundredTwelveDF_1783, prime_oneHundredTwelveDF_4079, prime_oneHundredTwelveDF_2017690943, prime_oneHundredTwelveDF_45804445331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499258 : Nat.totient 132413891019516111881272499258 = 60744322226077346691216046080 := by
  rw [← show ((([(2, 1), (13, 1), (311, 1), (383, 1), (4273, 1), (10006176146377349017, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_311, prime_oneHundredTwelveDF_383, prime_oneHundredTwelveDF_4273, prime_oneHundredTwelveDF_10006176146377349017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499259 : Nat.totient 132413891019516111881272499259 = 88275854222339344497759382560 := by
  rw [← show ((([(3, 1), (1311311, 1), (15206419, 1), (2213500557195517, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_1311311, prime_oneHundredTwelveDF_15206419, prime_oneHundredTwelveDF_2213500557195517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499260 : Nat.totient 132413891019516111881272499260 = 49661309039078441471840206848 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (139, 1), (353, 1), (3433, 1), (2068648210956352507, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_139, prime_oneHundredTwelveDF_353, prime_oneHundredTwelveDF_3433, prime_oneHundredTwelveDF_2068648210956352507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499261 : Nat.totient 132413891019516111881272499261 = 127411774961627613897926108640 := by
  rw [← show ((([(31, 2), (179, 1), (8599, 1), (74959583, 1), (1194213614807, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_31, prime_oneHundredTwelveDF_179, prime_oneHundredTwelveDF_8599, prime_oneHundredTwelveDF_74959583, prime_oneHundredTwelveDF_1194213614807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499262 : Nat.totient 132413891019516111881272499262 = 42031321358696316134825973408 := by
  rw [← show ((([(2, 1), (3, 3), (37, 1), (47, 1), (1410068483584820052832327, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_37, prime_oneHundredTwelveDF_47, prime_oneHundredTwelveDF_1410068483584820052832327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499263 : Nat.totient 132413891019516111881272499263 = 111425798073747816417923700480 := by
  rw [← show ((([(7, 1), (71, 1), (239, 1), (22307, 1), (1536649, 1), (32520964175027, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_71, prime_oneHundredTwelveDF_239, prime_oneHundredTwelveDF_22307, prime_oneHundredTwelveDF_1536649, prime_oneHundredTwelveDF_32520964175027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499264 : Nat.totient 132413891019516111881272499264 = 64667232023733921551485501440 := by
  rw [← show ((([(2, 6), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_43, prime_oneHundredTwelveDF_4282273, prime_oneHundredTwelveDF_32701811, prime_oneHundredTwelveDF_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499265 : Nat.totient 132413891019516111881272499265 = 67766409527738100983749370880 := by
  rw [← show ((([(3, 1), (5, 1), (29, 1), (163, 1), (82837, 1), (1350641519, 1), (16691379371, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_29, prime_oneHundredTwelveDF_163, prime_oneHundredTwelveDF_82837, prime_oneHundredTwelveDF_1350641519, prime_oneHundredTwelveDF_16691379371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499266 : Nat.totient 132413891019516111881272499266 = 66206945509575250356784661040 := by
  rw [← show ((([(2, 1), (362172069821, 1), (182805221679518773, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_362172069821, prime_oneHundredTwelveDF_182805221679518773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499267 : Nat.totient 132413891019516111881272499267 = 120376264563196465346611362960 := by
  rw [← show ((([(11, 1), (12037626456319646534661136297, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_12037626456319646534661136297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499268 : Nat.totient 132413891019516111881272499268 = 44137883920014142428791808000 := by
  rw [← show ((([(2, 2), (3, 1), (553601, 1), (1815083779, 1), (10981426522441, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_553601, prime_oneHundredTwelveDF_1815083779, prime_oneHundredTwelveDF_10981426522441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499269 : Nat.totient 132413891019516111881272499269 = 132413251909634252620014871920 := by
  rw [← show ((([(207197, 1), (3535965571, 1), (180734914054787, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_207197, prime_oneHundredTwelveDF_3535965571, prime_oneHundredTwelveDF_180734914054787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499270 : Nat.totient 132413891019516111881272499270 = 45194347594773677087878717440 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_271, prime_oneHundredTwelveDF_1217, prime_oneHundredTwelveDF_4440187, prime_oneHundredTwelveDF_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499271 : Nat.totient 132413891019516111881272499271 = 76692208280384565524354946048 := by
  rw [← show ((([(3, 2), (13, 1), (17, 1), (825447703, 1), (80650896845808413, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_825447703, prime_oneHundredTwelveDF_80650896845808413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499272 : Nat.totient 132413891019516111881272499272 = 66163128868123537041932976720 := by
  rw [← show ((([(2, 3), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_1511, prime_oneHundredTwelveDF_10954160408629724675816719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499273 : Nat.totient 132413891019516111881272499273 = 132413891019516111881272499272 := by
  rw [← show ((([(132413891019516111881272499273, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_132413891019516111881272499273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499274 : Nat.totient 132413891019516111881272499274 = 44137963673172037293757499756 := by
  rw [← show ((([(2, 1), (3, 1), (22068981836586018646878749879, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_22068981836586018646878749879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499275 : Nat.totient 132413891019516111881272499275 = 105931112815612889505017999400 := by
  rw [← show ((([(5, 2), (5296555640780644475250899971, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_5296555640780644475250899971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499276 : Nat.totient 132413891019516111881272499276 = 65879289261905094019460630144 := by
  rw [← show ((([(2, 2), (269, 1), (809, 1), (152115249699610919765639, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_269, prime_oneHundredTwelveDF_809, prime_oneHundredTwelveDF_152115249699610919765639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499277 : Nat.totient 132413891019516111881272499277 = 74747830567296843504371367936 := by
  rw [← show ((([(3, 1), (7, 1), (83, 1), (13627, 1), (560969, 1), (21727217, 1), (457396609, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_83, prime_oneHundredTwelveDF_13627, prime_oneHundredTwelveDF_560969, prime_oneHundredTwelveDF_21727217, prime_oneHundredTwelveDF_457396609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499278 : Nat.totient 132413891019516111881272499278 = 57570959588203826361277755360 := by
  rw [← show ((([(2, 1), (11, 1), (23, 1), (193597, 1), (1351712741721838410479, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_23, prime_oneHundredTwelveDF_193597, prime_oneHundredTwelveDF_1351712741721838410479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499279 : Nat.totient 132413891019516111881272499279 = 125154281066743551483327006720 := by
  rw [← show ((([(19, 1), (439, 1), (31337, 1), (286073, 1), (454799, 1), (3893692381, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_439, prime_oneHundredTwelveDF_31337, prime_oneHundredTwelveDF_286073, prime_oneHundredTwelveDF_454799, prime_oneHundredTwelveDF_3893692381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499280 : Nat.totient 132413891019516111881272499280 = 35310132617445547666442035200 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_148193, prime_oneHundredTwelveDF_732506743, prime_oneHundredTwelveDF_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499281 : Nat.totient 132413891019516111881272499281 = 132413891019516111881272499280 := by
  rw [← show ((([(132413891019516111881272499281, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_132413891019516111881272499281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499282 : Nat.totient 132413891019516111881272499282 = 66171415365472025102995657728 := by
  rw [← show ((([(2, 1), (1999, 1), (27457, 1), (3018872029, 1), (399570089203, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_1999, prime_oneHundredTwelveDF_27457, prime_oneHundredTwelveDF_3018872029, prime_oneHundredTwelveDF_399570089203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499283 : Nat.totient 132413891019516111881272499283 = 88168404901275480512790816000 := by
  rw [← show ((([(3, 1), (821, 1), (1362244893221, 1), (39465167216521, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_821, prime_oneHundredTwelveDF_1362244893221, prime_oneHundredTwelveDF_39465167216521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499284 : Nat.totient 132413891019516111881272499284 = 51297706743638903344613376000 := by
  rw [← show ((([(2, 2), (7, 2), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_101, prime_oneHundredTwelveDF_103, prime_oneHundredTwelveDF_1163, prime_oneHundredTwelveDF_3221, prime_oneHundredTwelveDF_20357, prime_oneHundredTwelveDF_53279, prime_oneHundredTwelveDF_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499285 : Nat.totient 132413891019516111881272499285 = 105931106639994031683779654080 := by
  rw [← show ((([(5, 1), (17153117, 1), (1543904714455292433221, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_17153117, prime_oneHundredTwelveDF_1543904714455292433221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499286 : Nat.totient 132413891019516111881272499286 = 44137963672707748023851220128 := by
  rw [← show ((([(2, 1), (3, 1), (95065694189, 1), (232144539887445629, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_95065694189, prime_oneHundredTwelveDF_232144539887445629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499287 : Nat.totient 132413891019516111881272499287 = 131570490439773971041264394040 := by
  rw [← show ((([(157, 1), (843400579742140840008105091, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_157, prime_oneHundredTwelveDF_843400579742140840008105091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499288 : Nat.totient 132413891019516111881272499288 = 62225738365355018733967022592 := by
  rw [← show ((([(2, 3), (17, 1), (719, 1), (4003579, 1), (338234065908919183, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_17, prime_oneHundredTwelveDF_719, prime_oneHundredTwelveDF_4003579, prime_oneHundredTwelveDF_338234065908919183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499289 : Nat.totient 132413891019516111881272499289 = 80239849400101049601846868800 := by
  rw [← show ((([(3, 3), (11, 1), (7459, 1), (341863, 1), (174841446850172461, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_7459, prime_oneHundredTwelveDF_341863, prime_oneHundredTwelveDF_174841446850172461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499290 : Nat.totient 132413891019516111881272499290 = 52844391614424548101740940800 := by
  rw [← show ((([(2, 1), (5, 1), (743, 1), (1733, 1), (2731, 1), (3765515772023157961, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_743, prime_oneHundredTwelveDF_1733, prime_oneHundredTwelveDF_2731, prime_oneHundredTwelveDF_3765515772023157961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499291 : Nat.totient 132413891019516111881272499291 = 110838031023036260392584220800 := by
  rw [← show ((([(7, 1), (67, 1), (131, 1), (991, 1), (633623, 1), (3432296688844733, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_67, prime_oneHundredTwelveDF_131, prime_oneHundredTwelveDF_991, prime_oneHundredTwelveDF_633623, prime_oneHundredTwelveDF_3432296688844733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499292 : Nat.totient 132413891019516111881272499292 = 42708719178010479269961704640 := by
  rw [← show ((([(2, 2), (3, 1), (31, 1), (7853, 1), (45326794848457377387887, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_31, prime_oneHundredTwelveDF_7853, prime_oneHundredTwelveDF_45326794848457377387887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499293 : Nat.totient 132413891019516111881272499293 = 132413891019515293540694443488 := by
  rw [← show ((([(222070223812357, 1), (596270354243449, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_222070223812357, prime_oneHundredTwelveDF_596270354243449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499294 : Nat.totient 132413891019516111881272499294 = 62364809788107261119068339200 := by
  rw [← show ((([(2, 1), (29, 1), (41, 1), (3828269, 1), (97204621, 1), (149634707627, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_29, prime_oneHundredTwelveDF_41, prime_oneHundredTwelveDF_3828269, prime_oneHundredTwelveDF_97204621, prime_oneHundredTwelveDF_149634707627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499295 : Nat.totient 132413891019516111881272499295 = 70620520129103290067375413760 := by
  rw [← show ((([(3, 1), (5, 1), (318473, 1), (27718496496200329254761, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_318473, prime_oneHundredTwelveDF_27718496496200329254761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499296 : Nat.totient 132413891019516111881272499296 = 66206945509758055940636249632 := by
  rw [← show ((([(2, 5), (4137934094359878496289765603, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_4137934094359878496289765603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499297 : Nat.totient 132413891019516111881272499297 = 119587969899582954042559645632 := by
  rw [← show ((([(13, 1), (53, 1), (359, 1), (535327898490469461943847, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_13, prime_oneHundredTwelveDF_53, prime_oneHundredTwelveDF_359, prime_oneHundredTwelveDF_535327898490469461943847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499298 : Nat.totient 132413891019516111881272499298 = 35634006641079505759508190720 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (19, 1), (173, 1), (207341, 1), (1541977758959001869, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_7, prime_oneHundredTwelveDF_19, prime_oneHundredTwelveDF_173, prime_oneHundredTwelveDF_207341, prime_oneHundredTwelveDF_1541977758959001869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499299 : Nat.totient 132413891019516111881272499299 = 126539041848822702189855498240 := by
  rw [← show ((([(37, 1), (59, 1), (1171, 1), (29483, 1), (1180174613, 1), (1488692417, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_37, prime_oneHundredTwelveDF_59, prime_oneHundredTwelveDF_1171, prime_oneHundredTwelveDF_29483, prime_oneHundredTwelveDF_1180174613, prime_oneHundredTwelveDF_1488692417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499300 : Nat.totient 132413891019516111881272499300 = 47541005751254856074368992000 := by
  rw [← show ((([(2, 2), (5, 2), (11, 2), (79, 1), (229300624307, 1), (604109755261, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_2, prime_oneHundredTwelveDF_5, prime_oneHundredTwelveDF_11, prime_oneHundredTwelveDF_79, prime_oneHundredTwelveDF_229300624307, prime_oneHundredTwelveDF_604109755261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwelveDF_132413891019516111881272499301 : Nat.totient 132413891019516111881272499301 = 84139476608121418951992068544 := by
  rw [← show ((([(3, 1), (23, 1), (283, 1), (37892057519, 1), (178957470887677, 1)] : List FactorBlock).map factorBlockValue).prod) = 132413891019516111881272499301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwelveDF_3, prime_oneHundredTwelveDF_23, prime_oneHundredTwelveDF_283, prime_oneHundredTwelveDF_37892057519, prime_oneHundredTwelveDF_178957470887677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwelveDF : certifiedKill 1 132413891019516111881272499199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwelveDF_132413891019516111881272499200, phi_oneHundredTwelveDF_132413891019516111881272499201, phi_oneHundredTwelveDF_132413891019516111881272499202,
    phi_oneHundredTwelveDF_132413891019516111881272499203, phi_oneHundredTwelveDF_132413891019516111881272499204, phi_oneHundredTwelveDF_132413891019516111881272499205,
    phi_oneHundredTwelveDF_132413891019516111881272499206, phi_oneHundredTwelveDF_132413891019516111881272499207, phi_oneHundredTwelveDF_132413891019516111881272499208,
    phi_oneHundredTwelveDF_132413891019516111881272499209, phi_oneHundredTwelveDF_132413891019516111881272499210, phi_oneHundredTwelveDF_132413891019516111881272499211,
    phi_oneHundredTwelveDF_132413891019516111881272499212, phi_oneHundredTwelveDF_132413891019516111881272499213, phi_oneHundredTwelveDF_132413891019516111881272499214,
    phi_oneHundredTwelveDF_132413891019516111881272499215, phi_oneHundredTwelveDF_132413891019516111881272499216, phi_oneHundredTwelveDF_132413891019516111881272499217,
    phi_oneHundredTwelveDF_132413891019516111881272499218, phi_oneHundredTwelveDF_132413891019516111881272499219, phi_oneHundredTwelveDF_132413891019516111881272499220,
    phi_oneHundredTwelveDF_132413891019516111881272499221, phi_oneHundredTwelveDF_132413891019516111881272499222, phi_oneHundredTwelveDF_132413891019516111881272499223,
    phi_oneHundredTwelveDF_132413891019516111881272499224, phi_oneHundredTwelveDF_132413891019516111881272499225, phi_oneHundredTwelveDF_132413891019516111881272499226,
    phi_oneHundredTwelveDF_132413891019516111881272499227, phi_oneHundredTwelveDF_132413891019516111881272499228, phi_oneHundredTwelveDF_132413891019516111881272499229,
    phi_oneHundredTwelveDF_132413891019516111881272499230, phi_oneHundredTwelveDF_132413891019516111881272499231, phi_oneHundredTwelveDF_132413891019516111881272499232,
    phi_oneHundredTwelveDF_132413891019516111881272499233, phi_oneHundredTwelveDF_132413891019516111881272499234, phi_oneHundredTwelveDF_132413891019516111881272499235,
    phi_oneHundredTwelveDF_132413891019516111881272499236, phi_oneHundredTwelveDF_132413891019516111881272499237, phi_oneHundredTwelveDF_132413891019516111881272499238,
    phi_oneHundredTwelveDF_132413891019516111881272499239, phi_oneHundredTwelveDF_132413891019516111881272499240, phi_oneHundredTwelveDF_132413891019516111881272499241,
    phi_oneHundredTwelveDF_132413891019516111881272499242, phi_oneHundredTwelveDF_132413891019516111881272499243, phi_oneHundredTwelveDF_132413891019516111881272499244,
    phi_oneHundredTwelveDF_132413891019516111881272499245, phi_oneHundredTwelveDF_132413891019516111881272499246, phi_oneHundredTwelveDF_132413891019516111881272499247,
    phi_oneHundredTwelveDF_132413891019516111881272499248, phi_oneHundredTwelveDF_132413891019516111881272499249, phi_oneHundredTwelveDF_132413891019516111881272499250,
    phi_oneHundredTwelveDF_132413891019516111881272499251, phi_oneHundredTwelveDF_132413891019516111881272499252, phi_oneHundredTwelveDF_132413891019516111881272499253,
    phi_oneHundredTwelveDF_132413891019516111881272499254, phi_oneHundredTwelveDF_132413891019516111881272499255, phi_oneHundredTwelveDF_132413891019516111881272499256,
    phi_oneHundredTwelveDF_132413891019516111881272499257, phi_oneHundredTwelveDF_132413891019516111881272499258, phi_oneHundredTwelveDF_132413891019516111881272499259,
    phi_oneHundredTwelveDF_132413891019516111881272499260, phi_oneHundredTwelveDF_132413891019516111881272499261, phi_oneHundredTwelveDF_132413891019516111881272499262,
    phi_oneHundredTwelveDF_132413891019516111881272499263, phi_oneHundredTwelveDF_132413891019516111881272499264, phi_oneHundredTwelveDF_132413891019516111881272499265,
    phi_oneHundredTwelveDF_132413891019516111881272499266, phi_oneHundredTwelveDF_132413891019516111881272499267, phi_oneHundredTwelveDF_132413891019516111881272499268,
    phi_oneHundredTwelveDF_132413891019516111881272499269, phi_oneHundredTwelveDF_132413891019516111881272499270, phi_oneHundredTwelveDF_132413891019516111881272499271,
    phi_oneHundredTwelveDF_132413891019516111881272499272, phi_oneHundredTwelveDF_132413891019516111881272499273, phi_oneHundredTwelveDF_132413891019516111881272499274,
    phi_oneHundredTwelveDF_132413891019516111881272499275, phi_oneHundredTwelveDF_132413891019516111881272499276, phi_oneHundredTwelveDF_132413891019516111881272499277,
    phi_oneHundredTwelveDF_132413891019516111881272499278, phi_oneHundredTwelveDF_132413891019516111881272499279, phi_oneHundredTwelveDF_132413891019516111881272499280,
    phi_oneHundredTwelveDF_132413891019516111881272499281, phi_oneHundredTwelveDF_132413891019516111881272499282, phi_oneHundredTwelveDF_132413891019516111881272499283,
    phi_oneHundredTwelveDF_132413891019516111881272499284, phi_oneHundredTwelveDF_132413891019516111881272499285, phi_oneHundredTwelveDF_132413891019516111881272499286,
    phi_oneHundredTwelveDF_132413891019516111881272499287, phi_oneHundredTwelveDF_132413891019516111881272499288, phi_oneHundredTwelveDF_132413891019516111881272499289,
    phi_oneHundredTwelveDF_132413891019516111881272499290, phi_oneHundredTwelveDF_132413891019516111881272499291, phi_oneHundredTwelveDF_132413891019516111881272499292,
    phi_oneHundredTwelveDF_132413891019516111881272499293, phi_oneHundredTwelveDF_132413891019516111881272499294, phi_oneHundredTwelveDF_132413891019516111881272499295,
    phi_oneHundredTwelveDF_132413891019516111881272499296, phi_oneHundredTwelveDF_132413891019516111881272499297, phi_oneHundredTwelveDF_132413891019516111881272499298,
    phi_oneHundredTwelveDF_132413891019516111881272499299, phi_oneHundredTwelveDF_132413891019516111881272499300, phi_oneHundredTwelveDF_132413891019516111881272499301
    ]

end TotientTailPeriodKiller
end Erdos249257
