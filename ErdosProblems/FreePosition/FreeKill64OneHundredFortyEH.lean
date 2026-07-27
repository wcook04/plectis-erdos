import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFortyEHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyEHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyEHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyEHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyEHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyEHFastPow a n * oneHundredFortyEHFastPow a n * a else oneHundredFortyEHFastPow a n * oneHundredFortyEHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyEH_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyEH_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyEH_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyEH_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyEH_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyEH_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyEH_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyEH_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyEH_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyEH_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyEH_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyEH_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyEH_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyEH_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyEH_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyEH_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyEH_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyEH_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyEH_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyEH_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyEH_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyEH_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyEH_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyEH_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyEH_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyEH_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyEH_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyEH_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyEH_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyEH_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyEH_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyEH_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyEH_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortyEH_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFortyEH_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyEH_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyEH_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyEH_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyEH_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFortyEH_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyEH_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyEH_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortyEH_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortyEH_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyEH_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortyEH_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortyEH_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFortyEH_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFortyEH_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyEH_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFortyEH_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyEH_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFortyEH_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyEH_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFortyEH_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyEH_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortyEH_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortyEH_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortyEH_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFortyEH_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFortyEH_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortyEH_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyEH_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortyEH_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortyEH_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyEH_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFortyEH_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortyEH_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortyEH_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFortyEH_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFortyEH_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFortyEH_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFortyEH_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFortyEH_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortyEH_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFortyEH_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFortyEH_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFortyEH_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFortyEH_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFortyEH_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFortyEH_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFortyEH_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFortyEH_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFortyEH_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFortyEH_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFortyEH_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFortyEH_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFortyEH_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyEH_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFortyEH_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFortyEH_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFortyEH_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFortyEH_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFortyEH_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredFortyEH_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFortyEH_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFortyEH_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFortyEH_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFortyEH_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFortyEH_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFortyEH_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFortyEH_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFortyEH_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFortyEH_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredFortyEH_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFortyEH_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredFortyEH_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredFortyEH_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFortyEH_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredFortyEH_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFortyEH_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFortyEH_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFortyEH_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFortyEH_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredFortyEH_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFortyEH_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredFortyEH_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFortyEH_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFortyEH_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFortyEH_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredFortyEH_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredFortyEH_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFortyEH_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFortyEH_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredFortyEH_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredFortyEH_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortyEH_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFortyEH_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredFortyEH_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFortyEH_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFortyEH_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredFortyEH_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFortyEH_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredFortyEH_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFortyEH_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredFortyEH_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredFortyEH_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredFortyEH_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredFortyEH_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredFortyEH_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredFortyEH_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredFortyEH_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredFortyEH_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredFortyEH_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFortyEH_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredFortyEH_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredFortyEH_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredFortyEH_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFortyEH_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredFortyEH_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredFortyEH_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFortyEH_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFortyEH_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredFortyEH_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFortyEH_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredFortyEH_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredFortyEH_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredFortyEH_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredFortyEH_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredFortyEH_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredFortyEH_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredFortyEH_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_oneHundredFortyEH_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredFortyEH_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_oneHundredFortyEH_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_oneHundredFortyEH_3061 : Nat.Prime 3061 := by norm_num

private theorem prime_oneHundredFortyEH_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_oneHundredFortyEH_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredFortyEH_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredFortyEH_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredFortyEH_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredFortyEH_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredFortyEH_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredFortyEH_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_oneHundredFortyEH_3557 : Nat.Prime 3557 := by norm_num

private theorem prime_oneHundredFortyEH_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredFortyEH_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredFortyEH_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredFortyEH_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredFortyEH_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredFortyEH_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredFortyEH_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredFortyEH_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredFortyEH_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_oneHundredFortyEH_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredFortyEH_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredFortyEH_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredFortyEH_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredFortyEH_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredFortyEH_4759 : Nat.Prime 4759 := by norm_num

private theorem prime_oneHundredFortyEH_5011 : Nat.Prime 5011 := by norm_num

private theorem prime_oneHundredFortyEH_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_oneHundredFortyEH_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredFortyEH_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_oneHundredFortyEH_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_oneHundredFortyEH_5507 : Nat.Prime 5507 := by norm_num

private theorem prime_oneHundredFortyEH_5813 : Nat.Prime 5813 := by norm_num

private theorem prime_oneHundredFortyEH_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredFortyEH_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_oneHundredFortyEH_6551 : Nat.Prime 6551 := by norm_num

private theorem prime_oneHundredFortyEH_6823 : Nat.Prime 6823 := by norm_num

private theorem prime_oneHundredFortyEH_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_oneHundredFortyEH_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredFortyEH_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredFortyEH_7817 : Nat.Prime 7817 := by norm_num

private theorem prime_oneHundredFortyEH_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_oneHundredFortyEH_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFortyEH_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_oneHundredFortyEH_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredFortyEH_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredFortyEH_8783 : Nat.Prime 8783 := by norm_num

private theorem prime_oneHundredFortyEH_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredFortyEH_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_oneHundredFortyEH_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredFortyEH_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredFortyEH_10427 : Nat.Prime 10427 := by norm_num

private theorem prime_oneHundredFortyEH_10771 : Nat.Prime 10771 := by norm_num

private theorem prime_oneHundredFortyEH_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredFortyEH_10853 : Nat.Prime 10853 := by norm_num

private theorem prime_oneHundredFortyEH_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredFortyEH_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredFortyEH_11677 : Nat.Prime 11677 := by norm_num

private theorem prime_oneHundredFortyEH_12263 : Nat.Prime 12263 := by norm_num

private theorem prime_oneHundredFortyEH_12409 : Nat.Prime 12409 := by norm_num

private theorem prime_oneHundredFortyEH_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredFortyEH_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_oneHundredFortyEH_13859 : Nat.Prime 13859 := by norm_num

private theorem prime_oneHundredFortyEH_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_oneHundredFortyEH_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredFortyEH_15031 : Nat.Prime 15031 := by norm_num

private theorem prime_oneHundredFortyEH_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredFortyEH_15971 : Nat.Prime 15971 := by norm_num

private theorem prime_oneHundredFortyEH_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredFortyEH_16787 : Nat.Prime 16787 := by norm_num

private theorem prime_oneHundredFortyEH_17053 : Nat.Prime 17053 := by norm_num

private theorem prime_oneHundredFortyEH_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyEH_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredFortyEH_17351 : Nat.Prime 17351 := by norm_num

private theorem prime_oneHundredFortyEH_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredFortyEH_17579 : Nat.Prime 17579 := by norm_num

private theorem prime_oneHundredFortyEH_18181 : Nat.Prime 18181 := by norm_num

private theorem prime_oneHundredFortyEH_20113 : Nat.Prime 20113 := by norm_num

private theorem prime_oneHundredFortyEH_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyEH_22247 : Nat.Prime 22247 := by norm_num

private theorem prime_oneHundredFortyEH_23609 : Nat.Prime 23609 := by norm_num

private theorem prime_oneHundredFortyEH_23833 : Nat.Prime 23833 := by norm_num

private theorem prime_oneHundredFortyEH_24179 : Nat.Prime 24179 := by norm_num

private theorem prime_oneHundredFortyEH_24967 : Nat.Prime 24967 := by norm_num

private theorem prime_oneHundredFortyEH_25243 : Nat.Prime 25243 := by norm_num

private theorem prime_oneHundredFortyEH_25343 : Nat.Prime 25343 := by norm_num

private theorem prime_oneHundredFortyEH_25471 : Nat.Prime 25471 := by norm_num

private theorem prime_oneHundredFortyEH_25889 : Nat.Prime 25889 := by norm_num

private theorem prime_oneHundredFortyEH_25919 : Nat.Prime 25919 := by norm_num

private theorem prime_oneHundredFortyEH_26251 : Nat.Prime 26251 := by norm_num

private theorem prime_oneHundredFortyEH_26513 : Nat.Prime 26513 := by norm_num

private theorem prime_oneHundredFortyEH_27799 : Nat.Prime 27799 := by norm_num

private theorem prime_oneHundredFortyEH_28163 : Nat.Prime 28163 := by norm_num

private theorem prime_oneHundredFortyEH_28663 : Nat.Prime 28663 := by norm_num

private theorem prime_oneHundredFortyEH_29251 : Nat.Prime 29251 := by norm_num

private theorem prime_oneHundredFortyEH_29327 : Nat.Prime 29327 := by norm_num

private theorem prime_oneHundredFortyEH_29437 : Nat.Prime 29437 := by norm_num

private theorem prime_oneHundredFortyEH_31033 : Nat.Prime 31033 := by norm_num

private theorem prime_oneHundredFortyEH_31277 : Nat.Prime 31277 := by norm_num

private theorem prime_oneHundredFortyEH_31327 : Nat.Prime 31327 := by norm_num

private theorem prime_oneHundredFortyEH_36107 : Nat.Prime 36107 := by norm_num

private theorem prime_oneHundredFortyEH_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredFortyEH_37019 : Nat.Prime 37019 := by norm_num

private theorem prime_oneHundredFortyEH_37357 : Nat.Prime 37357 := by norm_num

private theorem prime_oneHundredFortyEH_37991 : Nat.Prime 37991 := by norm_num

private theorem prime_oneHundredFortyEH_38959 : Nat.Prime 38959 := by norm_num

private theorem prime_oneHundredFortyEH_39343 : Nat.Prime 39343 := by norm_num

private theorem prime_oneHundredFortyEH_41777 : Nat.Prime 41777 := by norm_num

private theorem prime_oneHundredFortyEH_41953 : Nat.Prime 41953 := by norm_num

private theorem prime_oneHundredFortyEH_42899 : Nat.Prime 42899 := by norm_num

private theorem prime_oneHundredFortyEH_43711 : Nat.Prime 43711 := by norm_num

private theorem prime_oneHundredFortyEH_44171 : Nat.Prime 44171 := by norm_num

private theorem prime_oneHundredFortyEH_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredFortyEH_46271 : Nat.Prime 46271 := by norm_num

private theorem prime_oneHundredFortyEH_46639 : Nat.Prime 46639 := by norm_num

private theorem prime_oneHundredFortyEH_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFortyEH_48131 : Nat.Prime 48131 := by norm_num

private theorem prime_oneHundredFortyEH_49123 : Nat.Prime 49123 := by norm_num

private theorem prime_oneHundredFortyEH_49823 : Nat.Prime 49823 := by norm_num

private theorem prime_oneHundredFortyEH_58963 : Nat.Prime 58963 := by norm_num

private theorem prime_oneHundredFortyEH_59113 : Nat.Prime 59113 := by norm_num

private theorem prime_oneHundredFortyEH_60493 : Nat.Prime 60493 := by norm_num

private theorem prime_oneHundredFortyEH_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredFortyEH_65257 : Nat.Prime 65257 := by norm_num

private theorem prime_oneHundredFortyEH_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFortyEH_70379 : Nat.Prime 70379 := by norm_num

private theorem prime_oneHundredFortyEH_74377 : Nat.Prime 74377 := by norm_num

private theorem prime_oneHundredFortyEH_76507 : Nat.Prime 76507 := by norm_num

private theorem prime_oneHundredFortyEH_87257 : Nat.Prime 87257 := by norm_num

private theorem prime_oneHundredFortyEH_92557 : Nat.Prime 92557 := by norm_num

private theorem prime_oneHundredFortyEH_94889 : Nat.Prime 94889 := by norm_num

private theorem prime_oneHundredFortyEH_96697 : Nat.Prime 96697 := by norm_num

private theorem prime_oneHundredFortyEH_101027 : Nat.Prime 101027 := by norm_num

private theorem prime_oneHundredFortyEH_103699 : Nat.Prime 103699 := by norm_num

private theorem prime_oneHundredFortyEH_109159 : Nat.Prime 109159 := by norm_num

private theorem prime_oneHundredFortyEH_109807 : Nat.Prime 109807 := by norm_num

private theorem prime_oneHundredFortyEH_113537 : Nat.Prime 113537 := by norm_num

private theorem prime_oneHundredFortyEH_121921 : Nat.Prime 121921 := by norm_num

private theorem prime_oneHundredFortyEH_140143 : Nat.Prime 140143 := by norm_num

private theorem prime_oneHundredFortyEH_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredFortyEH_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredFortyEH_151157 : Nat.Prime 151157 := by norm_num

private theorem prime_oneHundredFortyEH_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyEH_177323 : Nat.Prime 177323 := by norm_num

private theorem prime_oneHundredFortyEH_181891 : Nat.Prime 181891 := by norm_num

private theorem prime_oneHundredFortyEH_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredFortyEH_188021 : Nat.Prime 188021 := by norm_num

private theorem prime_oneHundredFortyEH_192497 : Nat.Prime 192497 := by norm_num

private theorem prime_oneHundredFortyEH_196051 : Nat.Prime 196051 := by norm_num

private theorem prime_oneHundredFortyEH_196081 : Nat.Prime 196081 := by norm_num

private theorem prime_oneHundredFortyEH_200639 : Nat.Prime 200639 := by norm_num

private theorem prime_oneHundredFortyEH_213929 : Nat.Prime 213929 := by norm_num

private theorem prime_oneHundredFortyEH_217457 : Nat.Prime 217457 := by norm_num

private theorem prime_oneHundredFortyEH_219547 : Nat.Prime 219547 := by norm_num

private theorem prime_oneHundredFortyEH_222613 : Nat.Prime 222613 := by norm_num

private theorem prime_oneHundredFortyEH_235397 : Nat.Prime 235397 := by norm_num

private theorem prime_oneHundredFortyEH_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredFortyEH_260419 : Nat.Prime 260419 := by norm_num

private theorem prime_oneHundredFortyEH_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredFortyEH_272809 : Nat.Prime 272809 := by norm_num

private theorem prime_oneHundredFortyEH_277577 : Nat.Prime 277577 := by norm_num

private theorem prime_oneHundredFortyEH_278437 : Nat.Prime 278437 := by norm_num

private theorem prime_oneHundredFortyEH_279029 : Nat.Prime 279029 := by norm_num

private theorem prime_oneHundredFortyEH_279709 : Nat.Prime 279709 := by norm_num

private theorem prime_oneHundredFortyEH_294703 : Nat.Prime 294703 := by norm_num

private theorem prime_oneHundredFortyEH_296489 : Nat.Prime 296489 := by norm_num

private theorem prime_oneHundredFortyEH_297779 : Nat.Prime 297779 := by norm_num

private theorem prime_oneHundredFortyEH_311743 : Nat.Prime 311743 := by norm_num

private theorem prime_oneHundredFortyEH_313409 : Nat.Prime 313409 := by norm_num

private theorem prime_oneHundredFortyEH_327581 : Nat.Prime 327581 := by norm_num

private theorem prime_oneHundredFortyEH_344237 : Nat.Prime 344237 := by norm_num

private theorem prime_oneHundredFortyEH_355343 : Nat.Prime 355343 := by norm_num

private theorem prime_oneHundredFortyEH_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredFortyEH_388187 : Nat.Prime 388187 := by norm_num

private theorem prime_oneHundredFortyEH_467941 : Nat.Prime 467941 := by norm_num

private theorem prime_oneHundredFortyEH_505823 : Nat.Prime 505823 := by norm_num

private theorem prime_oneHundredFortyEH_506327 : Nat.Prime 506327 := by norm_num

private theorem prime_oneHundredFortyEH_518047 : Nat.Prime 518047 := by norm_num

private theorem prime_oneHundredFortyEH_534851 : Nat.Prime 534851 := by norm_num

private theorem prime_oneHundredFortyEH_552677 : Nat.Prime 552677 := by norm_num

private theorem prime_oneHundredFortyEH_553601 : Nat.Prime 553601 := by norm_num

private theorem prime_oneHundredFortyEH_594023 : Nat.Prime 594023 := by norm_num

private theorem prime_oneHundredFortyEH_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredFortyEH_643781 : Nat.Prime 643781 := by norm_num

private theorem prime_oneHundredFortyEH_653647 : Nat.Prime 653647 := by norm_num

private theorem prime_oneHundredFortyEH_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredFortyEH_723133 : Nat.Prime 723133 := by norm_num

private theorem prime_oneHundredFortyEH_724277 : Nat.Prime 724277 := by norm_num

private theorem prime_oneHundredFortyEH_746371 : Nat.Prime 746371 := by norm_num

private theorem prime_oneHundredFortyEH_773693 : Nat.Prime 773693 := by norm_num

private theorem prime_oneHundredFortyEH_792107 : Nat.Prime 792107 := by norm_num

private theorem prime_oneHundredFortyEH_827423 : Nat.Prime 827423 := by norm_num

private theorem prime_oneHundredFortyEH_857453 : Nat.Prime 857453 := by norm_num

private theorem prime_oneHundredFortyEH_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredFortyEH_894059 : Nat.Prime 894059 := by norm_num

private theorem prime_oneHundredFortyEH_902389 : Nat.Prime 902389 := by norm_num

private theorem prime_oneHundredFortyEH_912539 : Nat.Prime 912539 := by norm_num

private theorem prime_oneHundredFortyEH_967709 : Nat.Prime 967709 := by norm_num

private theorem prime_oneHundredFortyEH_997813 : Nat.Prime 997813 := by norm_num

private theorem prime_oneHundredFortyEH_1052489 : Nat.Prime 1052489 := by norm_num

private theorem prime_oneHundredFortyEH_1079879 : Nat.Prime 1079879 := by norm_num

private theorem prime_oneHundredFortyEH_1174801 : Nat.Prime 1174801 := by norm_num

private theorem prime_oneHundredFortyEH_1200917 : Nat.Prime 1200917 := by norm_num

private theorem prime_oneHundredFortyEH_1287887 : Nat.Prime 1287887 := by norm_num

private theorem prime_oneHundredFortyEH_1290319 : Nat.Prime 1290319 := by norm_num

private theorem prime_oneHundredFortyEH_1403351 : Nat.Prime 1403351 := by norm_num

private theorem prime_oneHundredFortyEH_1445569 : Nat.Prime 1445569 := by norm_num

private theorem prime_oneHundredFortyEH_1463117 : Nat.Prime 1463117 := by norm_num

private theorem prime_oneHundredFortyEH_1524119 : Nat.Prime 1524119 := by norm_num

private theorem prime_oneHundredFortyEH_1592737 : Nat.Prime 1592737 := by norm_num

private theorem prime_oneHundredFortyEH_1673933 : Nat.Prime 1673933 := by norm_num

private theorem prime_oneHundredFortyEH_1731589 : Nat.Prime 1731589 := by norm_num

private theorem prime_oneHundredFortyEH_1781089 : Nat.Prime 1781089 := by norm_num

private theorem prime_oneHundredFortyEH_1812773 : Nat.Prime 1812773 := by norm_num

private theorem prime_oneHundredFortyEH_1817677 : Nat.Prime 1817677 := by norm_num

private theorem prime_oneHundredFortyEH_1844813 : Nat.Prime 1844813 := by norm_num

private theorem prime_oneHundredFortyEH_1861583 : Nat.Prime 1861583 := by norm_num

private theorem prime_oneHundredFortyEH_1868173 : Nat.Prime 1868173 := by norm_num

private theorem prime_oneHundredFortyEH_2011699 : Nat.Prime 2011699 := by norm_num

private theorem prime_oneHundredFortyEH_2115499 : Nat.Prime 2115499 := by norm_num

private theorem prime_oneHundredFortyEH_2174941 : Nat.Prime 2174941 := by norm_num

private theorem prime_oneHundredFortyEH_2276699 : Nat.Prime 2276699 := by norm_num

private theorem prime_oneHundredFortyEH_2349811 : Nat.Prime 2349811 := by norm_num

private theorem prime_oneHundredFortyEH_2433721 : Nat.Prime 2433721 := by norm_num

private theorem prime_oneHundredFortyEH_2473871 : Nat.Prime 2473871 := by norm_num

private theorem prime_oneHundredFortyEH_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredFortyEH_2500999 : Nat.Prime 2500999 := by norm_num

private theorem prime_oneHundredFortyEH_2506583 : Nat.Prime 2506583 := by norm_num

private theorem prime_oneHundredFortyEH_2585293 : Nat.Prime 2585293 := by norm_num

private theorem prime_oneHundredFortyEH_2663069 : Nat.Prime 2663069 := by norm_num

private theorem prime_oneHundredFortyEH_2692553 : Nat.Prime 2692553 := by norm_num

private theorem prime_oneHundredFortyEH_3069133 : Nat.Prime 3069133 := by norm_num

private theorem prime_oneHundredFortyEH_3249863 : Nat.Prime 3249863 := by norm_num

private theorem prime_oneHundredFortyEH_3432511 : Nat.Prime 3432511 := by norm_num

private theorem prime_oneHundredFortyEH_3559741 : Nat.Prime 3559741 := by norm_num

private theorem prime_oneHundredFortyEH_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredFortyEH_3701779 : Nat.Prime 3701779 := by norm_num

private theorem prime_oneHundredFortyEH_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredFortyEH_4406503 : Nat.Prime 4406503 := by norm_num

private theorem prime_oneHundredFortyEH_5428399 : Nat.Prime 5428399 := by norm_num

private theorem prime_oneHundredFortyEH_5539187 : Nat.Prime 5539187 := by norm_num

private theorem prime_oneHundredFortyEH_5770649 : Nat.Prime 5770649 := by norm_num

private theorem prime_oneHundredFortyEH_6039193 : Nat.Prime 6039193 := by norm_num

private theorem prime_oneHundredFortyEH_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredFortyEH_6502439 : Nat.Prime 6502439 := by norm_num

private theorem prime_oneHundredFortyEH_7563319 : Nat.Prime 7563319 := by norm_num

private theorem prime_oneHundredFortyEH_8751781 : Nat.Prime 8751781 := by norm_num

private theorem prime_oneHundredFortyEH_9464419 : Nat.Prime 9464419 := by norm_num

private theorem prime_oneHundredFortyEH_9532441 : Nat.Prime 9532441 := by norm_num

private theorem prime_oneHundredFortyEH_9554807 : Nat.Prime 9554807 := by norm_num

private theorem prime_oneHundredFortyEH_9736939 : Nat.Prime 9736939 := by norm_num

private theorem prime_oneHundredFortyEH_9877709 : Nat.Prime 9877709 := by norm_num

private theorem prime_oneHundredFortyEH_10333159 : Nat.Prime 10333159 := by norm_num

private theorem prime_oneHundredFortyEH_10792363 : Nat.Prime 10792363 := by norm_num

private theorem prime_oneHundredFortyEH_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyEH_11104427 : Nat.Prime 11104427 := by norm_num

private theorem prime_oneHundredFortyEH_11292583 : Nat.Prime 11292583 := by norm_num

private theorem prime_oneHundredFortyEH_11333351 : Nat.Prime 11333351 := by norm_num

private theorem prime_oneHundredFortyEH_11975311 : Nat.Prime 11975311 := by norm_num

private theorem prime_oneHundredFortyEH_12983963 : Nat.Prime 12983963 := by norm_num

private theorem prime_oneHundredFortyEH_13151923 : Nat.Prime 13151923 := by norm_num

private theorem prime_oneHundredFortyEH_13551917 : Nat.Prime 13551917 := by norm_num

private theorem prime_oneHundredFortyEH_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredFortyEH_14265577 : Nat.Prime 14265577 := by norm_num

private theorem prime_oneHundredFortyEH_14653213 : Nat.Prime 14653213 := by norm_num

private theorem prime_oneHundredFortyEH_14684977 : Nat.Prime 14684977 := by norm_num

private theorem prime_oneHundredFortyEH_15099979 : Nat.Prime 15099979 := by norm_num

private theorem prime_oneHundredFortyEH_15442087 : Nat.Prime 15442087 := by norm_num

private theorem prime_oneHundredFortyEH_15826513 : Nat.Prime 15826513 := by norm_num

private theorem prime_oneHundredFortyEH_16904983 : Nat.Prime 16904983 := by norm_num

private theorem prime_oneHundredFortyEH_17282623 : Nat.Prime 17282623 := by norm_num

private theorem prime_oneHundredFortyEH_18151967 : Nat.Prime 18151967 := by norm_num

private theorem prime_oneHundredFortyEH_19038707 : Nat.Prime 19038707 := by norm_num

private theorem prime_oneHundredFortyEH_19584371 : Nat.Prime 19584371 := by norm_num

private theorem prime_oneHundredFortyEH_22314497 : Nat.Prime 22314497 := by norm_num

private theorem prime_oneHundredFortyEH_29350187 : Nat.Prime 29350187 := by norm_num

private theorem prime_oneHundredFortyEH_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_31824613 : Nat.Prime 31824613 := by
  apply lucas_primality 31824613 (5 : ZMod 31824613)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (149, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (149, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) = 31824613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_149
      · exact prime_oneHundredFortyEH_349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31824613) ^ 15912306 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 10608204 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 1872036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 213588 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 91188 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_32035681 : Nat.Prime 32035681 := by
  apply lucas_primality 32035681 (7 : ZMod 32035681)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (22247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (22247, 1)] : List FactorBlock).map factorBlockValue).prod) = 32035681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_22247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 32035681) ^ 16017840 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32035681) ^ 10678560 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32035681) ^ 6407136 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32035681) ^ 1440 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_73
      · exact prime_oneHundredFortyEH_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_32976283 : Nat.Prime 32976283 := by
  apply lucas_primality 32976283 (2 : ZMod 32976283)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (103699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (103699, 1)] : List FactorBlock).map factorBlockValue).prod) = 32976283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_53
      · exact prime_oneHundredFortyEH_103699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32976283) ^ 16488141 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32976283) ^ 10992094 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32976283) ^ 622194 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32976283) ^ 318 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_33900637 : Nat.Prime 33900637 := by
  apply lucas_primality 33900637 (5 : ZMod 33900637)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (19, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (19, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) = 33900637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_1931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33900637) ^ 16950318 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33900637) ^ 11300212 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33900637) ^ 4842948 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33900637) ^ 3081876 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33900637) ^ 1784244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33900637) ^ 17556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_37223647 : Nat.Prime 37223647 := by
  apply lucas_primality 37223647 (5 : ZMod 37223647)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (213929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (213929, 1)] : List FactorBlock).map factorBlockValue).prod) = 37223647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_213929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37223647) ^ 18611823 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37223647) ^ 12407882 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37223647) ^ 1283574 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37223647) ^ 174 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_40993549 : Nat.Prime 40993549 := by
  apply lucas_primality 40993549 (2 : ZMod 40993549)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 2), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 2), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 40993549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_67
      · exact prime_oneHundredFortyEH_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40993549) ^ 20496774 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40993549) ^ 13664516 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40993549) ^ 611844 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40993549) ^ 53868 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_48503657 : Nat.Prime 48503657 := by
  apply lucas_primality 48503657 (3 : ZMod 48503657)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (41, 1), (43, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 48503657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48503657) ^ 24251828 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 2552824 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1183016 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 1127992 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48503657) ^ 267976 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_51923327 : Nat.Prime 51923327 := by
  apply lucas_primality 51923327 (7 : ZMod 51923327)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (9203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_9203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51923327) ^ 25961663 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 7417618 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 3994102 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 1674946 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 51923327) ^ 5642 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_52510687 : Nat.Prime 52510687 := by
  apply lucas_primality 52510687 (5 : ZMod 52510687)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) = 52510687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_8751781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52510687) ^ 26255343 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 17503562 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 6 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_55413389 : Nat.Prime 55413389 := by
  apply lucas_primality 55413389 (2 : ZMod 55413389)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (193, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod) = 55413389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_179
      · exact prime_oneHundredFortyEH_193
      · exact prime_oneHundredFortyEH_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55413389) ^ 27706694 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 309572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 287116 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55413389) ^ 138188 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_1811
      · exact prime_oneHundredFortyEH_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_63836281 : Nat.Prime 63836281 := by
  apply lucas_primality 63836281 (13 : ZMod 63836281)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (177323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (177323, 1)] : List FactorBlock).map factorBlockValue).prod) = 63836281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_177323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 63836281) ^ 31918140 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 63836281) ^ 21278760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 63836281) ^ 12767256 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 63836281) ^ 360 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_64887553 : Nat.Prime 64887553 := by
  apply lucas_primality 64887553 (5 : ZMod 64887553)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) = 64887553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_28163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64887553) ^ 32443776 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 64887553) ^ 21629184 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 64887553) ^ 2304 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_64925719 : Nat.Prime 64925719 := by
  apply lucas_primality 64925719 (6 : ZMod 64925719)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (31, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (31, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) = 64925719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_2441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 64925719) ^ 32462859 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 64925719) ^ 21641906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 64925719) ^ 5902338 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 64925719) ^ 4994286 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 64925719) ^ 2094378 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 64925719) ^ 26598 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_67902011 : Nat.Prime 67902011 := by
  apply lucas_primality 67902011 (2 : ZMod 67902011)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (53, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (53, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 67902011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_53
      · exact prime_oneHundredFortyEH_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67902011) ^ 33951005 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 13580402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 6172910 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 3573790 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 1281170 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 110770 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_70177871 : Nat.Prime 70177871 := by
  apply lucas_primality 70177871 (7 : ZMod 70177871)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 2), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 2), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 70177871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 70177871) ^ 35088935 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 70177871) ^ 14035574 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 70177871) ^ 10025410 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 70177871) ^ 4128110 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 70177871) ^ 20230 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_72107443 : Nat.Prime 72107443 := by
  apply lucas_primality 72107443 (5 : ZMod 72107443)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (233, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (233, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 72107443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_233
      · exact prime_oneHundredFortyEH_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72107443) ^ 36053721 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 72107443) ^ 24035814 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 72107443) ^ 6555222 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 72107443) ^ 309474 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 72107443) ^ 138402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_79763389 : Nat.Prime 79763389 := by
  apply lucas_primality 79763389 (2 : ZMod 79763389)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 79763389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79763389) ^ 39881694 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 26587796 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 4691964 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 1123428 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 14484 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_81816961 : Nat.Prime 81816961 := by
  apply lucas_primality 81816961 (11 : ZMod 81816961)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (43, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (43, 1), (991, 1)] : List FactorBlock).map factorBlockValue).prod) = 81816961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 81816961) ^ 40908480 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 81816961) ^ 27272320 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 81816961) ^ 16363392 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 81816961) ^ 1902720 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 81816961) ^ 82560 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_89710769 : Nat.Prime 89710769 := by
  apply lucas_primality 89710769 (3 : ZMod 89710769)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 89710769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_53
      · exact prime_oneHundredFortyEH_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89710769) ^ 44855384 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 12815824 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 5277104 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 1692656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 706384 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_92296627 : Nat.Prime 92296627 := by
  apply lucas_primality 92296627 (2 : ZMod 92296627)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (137, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (137, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 92296627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_47
      · exact prime_oneHundredFortyEH_137
      · exact prime_oneHundredFortyEH_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92296627) ^ 46148313 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92296627) ^ 30765542 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92296627) ^ 1963758 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92296627) ^ 673698 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92296627) ^ 38634 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_94376339 : Nat.Prime 94376339 := by
  apply lucas_primality 94376339 (2 : ZMod 94376339)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (217457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (217457, 1)] : List FactorBlock).map factorBlockValue).prod) = 94376339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_217457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94376339) ^ 47188169 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94376339) ^ 13482334 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94376339) ^ 3044398 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94376339) ^ 434 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_101299553 : Nat.Prime 101299553 := by
  apply lucas_primality 101299553 (3 : ZMod 101299553)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (109159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (109159, 1)] : List FactorBlock).map factorBlockValue).prod) = 101299553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_109159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 101299553) ^ 50649776 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101299553) ^ 3493088 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101299553) ^ 928 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_117689867 : Nat.Prime 117689867 := by
  apply lucas_primality 117689867 (2 : ZMod 117689867)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1200917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1200917, 1)] : List FactorBlock).map factorBlockValue).prod) = 117689867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_1200917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 117689867) ^ 58844933 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 117689867) ^ 16812838 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 117689867) ^ 98 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_120606533 : Nat.Prime 120606533 := by
  apply lucas_primality 120606533 (2 : ZMod 120606533)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (509, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (509, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) = 120606533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_37
      · exact prime_oneHundredFortyEH_509
      · exact prime_oneHundredFortyEH_1601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120606533) ^ 60303266 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120606533) ^ 3259636 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120606533) ^ 236948 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120606533) ^ 75332 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_158265131 : Nat.Prime 158265131 := by
  apply lucas_primality 158265131 (2 : ZMod 158265131)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158265131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_15826513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158265131) ^ 79132565 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 31653026 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 10 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_173131403 : Nat.Prime 173131403 := by
  apply lucas_primality 173131403 (2 : ZMod 173131403)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (388187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (388187, 1)] : List FactorBlock).map factorBlockValue).prod) = 173131403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_223
      · exact prime_oneHundredFortyEH_388187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173131403) ^ 86565701 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 173131403) ^ 776374 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 173131403) ^ 446 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_183832669 : Nat.Prime 183832669 := by
  apply lucas_primality 183832669 (2 : ZMod 183832669)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1447, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1447, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 183832669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_1447
      · exact prime_oneHundredFortyEH_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183832669) ^ 91916334 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 61277556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 127044 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 52092 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_188199383 : Nat.Prime 188199383 := by
  apply lucas_primality 188199383 (5 : ZMod 188199383)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (67, 1), (200639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (67, 1), (200639, 1)] : List FactorBlock).map factorBlockValue).prod) = 188199383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_67
      · exact prime_oneHundredFortyEH_200639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 188199383) ^ 94099691 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 188199383) ^ 26885626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 188199383) ^ 2808946 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 188199383) ^ 938 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_188752679 : Nat.Prime 188752679 := by
  apply lucas_primality 188752679 (11 : ZMod 188752679)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (94376339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (94376339, 1)] : List FactorBlock).map factorBlockValue).prod) = 188752679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_94376339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 188752679) ^ 94376339 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 188752679) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_207391477 : Nat.Prime 207391477 := by
  apply lucas_primality 207391477 (2 : ZMod 207391477)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17282623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17282623, 1)] : List FactorBlock).map factorBlockValue).prod) = 207391477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17282623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 207391477) ^ 103695738 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 207391477) ^ 69130492 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 207391477) ^ 12 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_210430769 : Nat.Prime 210430769 := by
  apply lucas_primality 210430769 (3 : ZMod 210430769)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13151923, 1)] : List FactorBlock).map factorBlockValue).prod) = 210430769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_13151923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 210430769) ^ 105215384 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 210430769) ^ 16 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_249653533 : Nat.Prime 249653533 := by
  apply lucas_primality 249653533 (2 : ZMod 249653533)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (173, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (173, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 249653533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_53
      · exact prime_oneHundredFortyEH_173
      · exact prime_oneHundredFortyEH_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249653533) ^ 124826766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 249653533) ^ 83217844 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 249653533) ^ 4710444 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 249653533) ^ 1443084 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 249653533) ^ 110028 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_273761701 : Nat.Prime 273761701 := by
  apply lucas_primality 273761701 (22 : ZMod 273761701)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (912539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (912539, 1)] : List FactorBlock).map factorBlockValue).prod) = 273761701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_912539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 273761701) ^ 136880850 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 273761701) ^ 91253900 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 273761701) ^ 54752340 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 273761701) ^ 300 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_286004167 : Nat.Prime 286004167 := by
  apply lucas_primality 286004167 (3 : ZMod 286004167)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (971, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (971, 1), (7013, 1)] : List FactorBlock).map factorBlockValue).prod) = 286004167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_971
      · exact prime_oneHundredFortyEH_7013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 286004167) ^ 143002083 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 286004167) ^ 95334722 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 286004167) ^ 40857738 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 286004167) ^ 294546 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 286004167) ^ 40782 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_319053557 : Nat.Prime 319053557 := by
  apply lucas_primality 319053557 (2 : ZMod 319053557)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) = 319053557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_79763389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 319053557) ^ 159526778 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 319053557) ^ 4 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_349426349 : Nat.Prime 349426349 := by
  apply lucas_primality 349426349 (2 : ZMod 349426349)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (1052489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (1052489, 1)] : List FactorBlock).map factorBlockValue).prod) = 349426349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_83
      · exact prime_oneHundredFortyEH_1052489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 349426349) ^ 174713174 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 349426349) ^ 4209956 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 349426349) ^ 332 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_351518777 : Nat.Prime 351518777 := by
  apply lucas_primality 351518777 (3 : ZMod 351518777)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1319, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1319, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) = 351518777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_1319
      · exact prime_oneHundredFortyEH_4759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 351518777) ^ 175759388 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 50216968 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 266504 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 73864 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_352878593 : Nat.Prime 352878593 := by
  apply lucas_primality 352878593 (3 : ZMod 352878593)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 15), (11, 2), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 15), (11, 2), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 352878593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 352878593) ^ 176439296 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352878593) ^ 32079872 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352878593) ^ 3964928 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_354122287 : Nat.Prime 354122287 := by
  apply lucas_primality 354122287 (3 : ZMod 354122287)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) = 354122287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_196081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 354122287) ^ 177061143 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 118040762 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 50588898 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 8235402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 1806 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_355416889 : Nat.Prime 355416889 := by
  apply lucas_primality 355416889 (17 : ZMod 355416889)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (467, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (467, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) = 355416889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_467
      · exact prime_oneHundredFortyEH_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 355416889) ^ 177708444 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 355416889) ^ 118472296 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 355416889) ^ 18706152 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 355416889) ^ 761064 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 355416889) ^ 212952 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_12539
      · exact prime_oneHundredFortyEH_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_376398767 : Nat.Prime 376398767 := by
  apply lucas_primality 376398767 (5 : ZMod 376398767)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (188199383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (188199383, 1)] : List FactorBlock).map factorBlockValue).prod) = 376398767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_188199383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 376398767) ^ 188199383 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 376398767) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_381138661 : Nat.Prime 381138661 := by
  apply lucas_primality 381138661 (2 : ZMod 381138661)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 2), (79, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 2), (79, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 381138661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_79
      · exact prime_oneHundredFortyEH_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 381138661) ^ 190569330 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 381138661) ^ 127046220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 381138661) ^ 76227732 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 381138661) ^ 54448380 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 381138661) ^ 4824540 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 381138661) ^ 696780 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_384652063 : Nat.Prime 384652063 := by
  apply lucas_primality 384652063 (5 : ZMod 384652063)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (196051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (196051, 1)] : List FactorBlock).map factorBlockValue).prod) = 384652063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_109
      · exact prime_oneHundredFortyEH_196051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 384652063) ^ 192326031 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 128217354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 3528918 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 384652063) ^ 1962 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_427967311 : Nat.Prime 427967311 := by
  apply lucas_primality 427967311 (7 : ZMod 427967311)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (14265577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (14265577, 1)] : List FactorBlock).map factorBlockValue).prod) = 427967311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_14265577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 427967311) ^ 213983655 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 142655770 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 85593462 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 30 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_488478559 : Nat.Prime 488478559 := by
  apply lucas_primality 488478559 (3 : ZMod 488478559)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (433, 1), (188021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (433, 1), (188021, 1)] : List FactorBlock).map factorBlockValue).prod) = 488478559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_433
      · exact prime_oneHundredFortyEH_188021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 488478559) ^ 244239279 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488478559) ^ 162826186 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488478559) ^ 1128126 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488478559) ^ 2598 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_545326447 : Nat.Prime 545326447 := by
  apply lucas_primality 545326447 (6 : ZMod 545326447)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) = 545326447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_12983963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 545326447) ^ 272663223 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 181775482 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 77903778 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 42 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_545363909 : Nat.Prime 545363909 := by
  apply lucas_primality 545363909 (2 : ZMod 545363909)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (127, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (127, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) = 545363909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_37019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 545363909) ^ 272681954 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 18805652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 4294204 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 14732 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_561422969 : Nat.Prime 561422969 := by
  apply lucas_primality 561422969 (3 : ZMod 561422969)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (70177871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (70177871, 1)] : List FactorBlock).map factorBlockValue).prod) = 561422969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_70177871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 561422969) ^ 280711484 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 561422969) ^ 8 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_583929901 : Nat.Prime 583929901 := by
  apply lucas_primality 583929901 (17 : ZMod 583929901)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (83, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (83, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) = 583929901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_83
      · exact prime_oneHundredFortyEH_7817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 583929901) ^ 291964950 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 583929901) ^ 194643300 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 583929901) ^ 116785980 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 583929901) ^ 7035300 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 583929901) ^ 74700 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_630418703 : Nat.Prime 630418703 := by
  apply lucas_primality 630418703 (5 : ZMod 630418703)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (2115499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (2115499, 1)] : List FactorBlock).map factorBlockValue).prod) = 630418703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_149
      · exact prime_oneHundredFortyEH_2115499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 630418703) ^ 315209351 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 630418703) ^ 4230998 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 630418703) ^ 298 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_633960727 : Nat.Prime 633960727 := by
  apply lucas_primality 633960727 (3 : ZMod 633960727)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (19, 1), (31, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (19, 1), (31, 1), (523, 1)] : List FactorBlock).map factorBlockValue).prod) = 633960727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 633960727) ^ 316980363 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 633960727) ^ 211320242 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 633960727) ^ 90565818 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 633960727) ^ 33366354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 633960727) ^ 20450346 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 633960727) ^ 1212162 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_669434911 : Nat.Prime 669434911 := by
  apply lucas_primality 669434911 (6 : ZMod 669434911)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (22314497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (22314497, 1)] : List FactorBlock).map factorBlockValue).prod) = 669434911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_22314497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 669434911) ^ 334717455 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 669434911) ^ 223144970 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 669434911) ^ 133886982 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 669434911) ^ 30 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_679311571 : Nat.Prime 679311571 := by
  apply lucas_primality 679311571 (2 : ZMod 679311571)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (127, 1), (25471, 1)] : List FactorBlock).map factorBlockValue).prod) = 679311571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_25471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 679311571) ^ 339655785 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 226437190 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 135862314 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 97044510 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 5348910 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 679311571) ^ 26670 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17203
      · exact prime_oneHundredFortyEH_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_723639199 : Nat.Prime 723639199 := by
  apply lucas_primality 723639199 (3 : ZMod 723639199)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (120606533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (120606533, 1)] : List FactorBlock).map factorBlockValue).prod) = 723639199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_120606533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 723639199) ^ 361819599 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 723639199) ^ 241213066 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 723639199) ^ 6 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_101
      · exact prime_oneHundredFortyEH_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_777122653 : Nat.Prime 777122653 := by
  apply lucas_primality 777122653 (7 : ZMod 777122653)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (419, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (419, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 777122653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_419
      · exact prime_oneHundredFortyEH_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 777122653) ^ 388561326 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 259040884 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 6119076 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 1854708 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 638556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_792988759 : Nat.Prime 792988759 := by
  apply lucas_primality 792988759 (6 : ZMod 792988759)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (14684977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (14684977, 1)] : List FactorBlock).map factorBlockValue).prod) = 792988759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_14684977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 792988759) ^ 396494379 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 792988759) ^ 264329586 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 792988759) ^ 54 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1014799789 : Nat.Prime 1014799789 := by
  apply lucas_primality 1014799789 (6 : ZMod 1014799789)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (379, 1), (74377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (379, 1), (74377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1014799789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_379
      · exact prime_oneHundredFortyEH_74377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1014799789) ^ 507399894 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1014799789) ^ 338266596 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1014799789) ^ 2677572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1014799789) ^ 13644 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1028939279 : Nat.Prime 1028939279 := by
  apply lucas_primality 1028939279 (7 : ZMod 1028939279)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12263, 1), (41953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12263, 1), (41953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028939279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_12263
      · exact prime_oneHundredFortyEH_41953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1028939279) ^ 514469639 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1028939279) ^ 83906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1028939279) ^ 24526 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1097194663 : Nat.Prime 1097194663 := by
  apply lucas_primality 1097194663 (3 : ZMod 1097194663)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2521, 1), (24179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2521, 1), (24179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097194663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2521
      · exact prime_oneHundredFortyEH_24179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1097194663) ^ 548597331 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097194663) ^ 365731554 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097194663) ^ 435222 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1097194663) ^ 45378 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1144016669 : Nat.Prime 1144016669 := by
  apply lucas_primality 1144016669 (2 : ZMod 1144016669)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (286004167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (286004167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1144016669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_286004167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1144016669) ^ 572008334 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1144016669) ^ 4 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1333644841 : Nat.Prime 1333644841 := by
  apply lucas_primality 1333644841 (19 : ZMod 1333644841)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (307, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (307, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1333644841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_307
      · exact prime_oneHundredFortyEH_1097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1333644841) ^ 666822420 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 1333644841) ^ 444548280 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 1333644841) ^ 266728968 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 1333644841) ^ 121240440 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 1333644841) ^ 4344120 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 1333644841) ^ 1215720 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1678038433 : Nat.Prime 1678038433 := by
  apply lucas_primality 1678038433 (5 : ZMod 1678038433)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678038433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_109
      · exact prime_oneHundredFortyEH_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1678038433) ^ 839019216 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 559346144 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 239719776 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 54130272 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 15394848 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 2270688 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1785955307 : Nat.Prime 1785955307 := by
  apply lucas_primality 1785955307 (2 : ZMod 1785955307)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8839, 1), (101027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8839, 1), (101027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1785955307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_8839
      · exact prime_oneHundredFortyEH_101027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1785955307) ^ 892977653 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785955307) ^ 202054 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785955307) ^ 17678 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1815083779 : Nat.Prime 1815083779 := by
  apply lucas_primality 1815083779 (3 : ZMod 1815083779)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1815083779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_773693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1815083779) ^ 907541889 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 605027926 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 106769634 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 78916686 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 2346 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1950831163 : Nat.Prime 1950831163 := by
  apply lucas_primality 1950831163 (2 : ZMod 1950831163)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (47, 1), (109807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (47, 1), (109807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1950831163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_47
      · exact prime_oneHundredFortyEH_109807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1950831163) ^ 975415581 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1950831163) ^ 650277054 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1950831163) ^ 278690166 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1950831163) ^ 41507046 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1950831163) ^ 17766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2044098839 : Nat.Prime 2044098839 := by
  apply lucas_primality 2044098839 (17 : ZMod 2044098839)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10771, 1), (94889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10771, 1), (94889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2044098839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_10771
      · exact prime_oneHundredFortyEH_94889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 2044098839) ^ 1022049419 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2044098839) ^ 189778 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2044098839) ^ 21542 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2212469803 : Nat.Prime 2212469803 := by
  apply lucas_primality 2212469803 (2 : ZMod 2212469803)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (505823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (505823, 1)] : List FactorBlock).map factorBlockValue).prod) = 2212469803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_505823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2212469803) ^ 1106234901 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2212469803) ^ 737489934 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2212469803) ^ 4374 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2213346269 : Nat.Prime 2213346269 := by
  apply lucas_primality 2213346269 (2 : ZMod 2213346269)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11292583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2213346269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11292583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2213346269) ^ 1106673134 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 316192324 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2213346269) ^ 196 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2397312559 : Nat.Prime 2397312559 := by
  apply lucas_primality 2397312559 (3 : ZMod 2397312559)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (691, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (691, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397312559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_691
      · exact prime_oneHundredFortyEH_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2397312559) ^ 1198656279 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397312559) ^ 799104186 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397312559) ^ 58471038 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397312559) ^ 3469338 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397312559) ^ 1529874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_47
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2503484351 : Nat.Prime 2503484351 := by
  apply lucas_primality 2503484351 (19 : ZMod 2503484351)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (107, 1), (467941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (107, 1), (467941, 1)] : List FactorBlock).map factorBlockValue).prod) = 2503484351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_107
      · exact prime_oneHundredFortyEH_467941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2503484351) ^ 1251742175 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 500696870 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 23397050 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 5350 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2737617011 : Nat.Prime 2737617011 := by
  apply lucas_primality 2737617011 (2 : ZMod 2737617011)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (273761701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (273761701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2737617011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_273761701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2737617011) ^ 1368808505 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2737617011) ^ 547523402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2737617011) ^ 10 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2802634271 : Nat.Prime 2802634271 := by
  apply lucas_primality 2802634271 (13 : ZMod 2802634271)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (541, 1), (518047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (541, 1), (518047, 1)] : List FactorBlock).map factorBlockValue).prod) = 2802634271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_541
      · exact prime_oneHundredFortyEH_518047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2802634271) ^ 1401317135 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2802634271) ^ 560526854 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2802634271) ^ 5180470 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2802634271) ^ 5410 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3760996957 : Nat.Prime 3760996957 := by
  apply lucas_primality 3760996957 (22 : ZMod 3760996957)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (619, 1), (506327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (619, 1), (506327, 1)] : List FactorBlock).map factorBlockValue).prod) = 3760996957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_619
      · exact prime_oneHundredFortyEH_506327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 3760996957) ^ 1880498478 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 3760996957) ^ 1253665652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 3760996957) ^ 6075924 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (22 : ZMod 3760996957) ^ 7428 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3909625001 : Nat.Prime 3909625001 := by
  apply lucas_primality 3909625001 (3 : ZMod 3909625001)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 6), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 6), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3909625001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_31277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3909625001) ^ 1954812500 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3909625001) ^ 781925000 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3909625001) ^ 125000 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4171314503 : Nat.Prime 4171314503 := by
  apply lucas_primality 4171314503 (5 : ZMod 4171314503)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (48503657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4171314503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_48503657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4171314503) ^ 2085657251 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 97007314 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4171314503) ^ 86 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4725961831 : Nat.Prime 4725961831 := by
  apply lucas_primality 4725961831 (3 : ZMod 4725961831)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) = 4725961831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_52510687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4725961831) ^ 2362980915 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 1575320610 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 945192366 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 90 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4940300303 : Nat.Prime 4940300303 := by
  apply lucas_primality 4940300303 (5 : ZMod 4940300303)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (352878593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (352878593, 1)] : List FactorBlock).map factorBlockValue).prod) = 4940300303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_352878593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4940300303) ^ 2470150151 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4940300303) ^ 705757186 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4940300303) ^ 14 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5276183617 : Nat.Prime 5276183617 := by
  apply lucas_primality 5276183617 (7 : ZMod 5276183617)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5276183617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5276183617) ^ 2638091808 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 1758727872 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 479653056 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 19008 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5715236383 : Nat.Prime 5715236383 := by
  apply lucas_primality 5715236383 (3 : ZMod 5715236383)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (4049, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (4049, 1), (5471, 1)] : List FactorBlock).map factorBlockValue).prod) = 5715236383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_4049
      · exact prime_oneHundredFortyEH_5471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5715236383) ^ 2857618191 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5715236383) ^ 1905078794 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5715236383) ^ 132912474 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5715236383) ^ 1411518 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5715236383) ^ 1044642 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5886061981 : Nat.Prime 5886061981 := by
  apply lucas_primality 5886061981 (18 : ZMod 5886061981)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) = 5886061981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_5770649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 5886061981) ^ 2943030990 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1962020660 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1177212396 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 346238940 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1020 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6267714769 : Nat.Prime 6267714769 := by
  apply lucas_primality 6267714769 (11 : ZMod 6267714769)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (17, 1), (121921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (17, 1), (121921, 1)] : List FactorBlock).map factorBlockValue).prod) = 6267714769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_121921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6267714769) ^ 3133857384 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6267714769) ^ 2089238256 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6267714769) ^ 895387824 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6267714769) ^ 368689104 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 6267714769) ^ 51408 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6351455399 : Nat.Prime 6351455399 := by
  apply lucas_primality 6351455399 (7 : ZMod 6351455399)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1733, 1), (59113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1733, 1), (59113, 1)] : List FactorBlock).map factorBlockValue).prod) = 6351455399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_1733
      · exact prime_oneHundredFortyEH_59113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6351455399) ^ 3175727699 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6351455399) ^ 204885658 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6351455399) ^ 3665006 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6351455399) ^ 107446 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_311
      · exact prime_oneHundredFortyEH_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_7345893133 : Nat.Prime 7345893133 := by
  apply lucas_primality 7345893133 (5 : ZMod 7345893133)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (43, 1), (67, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (43, 1), (67, 1), (23609, 1)] : List FactorBlock).map factorBlockValue).prod) = 7345893133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_67
      · exact prime_oneHundredFortyEH_23609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7345893133) ^ 3672946566 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7345893133) ^ 2448631044 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7345893133) ^ 170834724 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7345893133) ^ 109640196 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7345893133) ^ 311148 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_9630796957 : Nat.Prime 9630796957 := by
  apply lucas_primality 9630796957 (2 : ZMod 9630796957)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (137, 1), (31327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (137, 1), (31327, 1)] : List FactorBlock).map factorBlockValue).prod) = 9630796957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_137
      · exact prime_oneHundredFortyEH_31327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9630796957) ^ 4815398478 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9630796957) ^ 3210265652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9630796957) ^ 875526996 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9630796957) ^ 566517468 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9630796957) ^ 70297788 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9630796957) ^ 307428 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_9880600607 : Nat.Prime 9880600607 := by
  apply lucas_primality 9880600607 (5 : ZMod 9880600607)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4940300303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4940300303, 1)] : List FactorBlock).map factorBlockValue).prod) = 9880600607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_4940300303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 9880600607) ^ 4940300303 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9880600607) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_14026408709 : Nat.Prime 14026408709 := by
  apply lucas_primality 14026408709 (2 : ZMod 14026408709)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026408709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_83
      · exact prime_oneHundredFortyEH_3249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14026408709) ^ 7013204354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 1078954516 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 168992876 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 4316 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_16350037229 : Nat.Prime 16350037229 := by
  apply lucas_primality 16350037229 (2 : ZMod 16350037229)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (583929901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (583929901, 1)] : List FactorBlock).map factorBlockValue).prod) = 16350037229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_583929901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16350037229) ^ 8175018614 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16350037229) ^ 2335719604 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16350037229) ^ 28 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_18624601987 : Nat.Prime 18624601987 := by
  apply lucas_primality 18624601987 (3 : ZMod 18624601987)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1321, 1), (2349811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1321, 1), (2349811, 1)] : List FactorBlock).map factorBlockValue).prod) = 18624601987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_1321
      · exact prime_oneHundredFortyEH_2349811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18624601987) ^ 9312300993 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18624601987) ^ 6208200662 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18624601987) ^ 14098866 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18624601987) ^ 7926 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_20720264519 : Nat.Prime 20720264519 := by
  apply lucas_primality 20720264519 (11 : ZMod 20720264519)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (19584371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (19584371, 1)] : List FactorBlock).map factorBlockValue).prod) = 20720264519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_19584371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 20720264519) ^ 10360132259 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 20720264519) ^ 900881066 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 20720264519) ^ 1058 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_22860945533 : Nat.Prime 22860945533 := by
  apply lucas_primality 22860945533 (2 : ZMod 22860945533)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5715236383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5715236383, 1)] : List FactorBlock).map factorBlockValue).prod) = 22860945533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5715236383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22860945533) ^ 11430472766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22860945533) ^ 4 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_22910475971 : Nat.Prime 22910475971 := by
  apply lucas_primality 22910475971 (2 : ZMod 22910475971)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (46639, 1), (49123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (46639, 1), (49123, 1)] : List FactorBlock).map factorBlockValue).prod) = 22910475971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_46639
      · exact prime_oneHundredFortyEH_49123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22910475971) ^ 11455237985 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22910475971) ^ 4582095194 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22910475971) ^ 491230 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22910475971) ^ 466390 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_23096547757 : Nat.Prime 23096547757 := by
  apply lucas_primality 23096547757 (5 : ZMod 23096547757)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (163, 1), (49823, 1)] : List FactorBlock).map factorBlockValue).prod) = 23096547757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_79
      · exact prime_oneHundredFortyEH_163
      · exact prime_oneHundredFortyEH_49823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23096547757) ^ 11548273878 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 7698849252 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 292361364 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 141696612 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 23096547757) ^ 463572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_24529186069 : Nat.Prime 24529186069 := by
  apply lucas_primality 24529186069 (2 : ZMod 24529186069)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2044098839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2044098839, 1)] : List FactorBlock).map factorBlockValue).prod) = 24529186069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2044098839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24529186069) ^ 12264593034 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24529186069) ^ 8176395356 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24529186069) ^ 12 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_24740943389 : Nat.Prime 24740943389 := by
  apply lucas_primality 24740943389 (2 : ZMod 24740943389)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (31, 1), (109, 1), (37357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (31, 1), (109, 1), (37357, 1)] : List FactorBlock).map factorBlockValue).prod) = 24740943389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_109
      · exact prime_oneHundredFortyEH_37357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24740943389) ^ 12370471694 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 3534420484 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 798094948 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 226981132 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 662284 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_26549637637 : Nat.Prime 26549637637 := by
  apply lucas_primality 26549637637 (2 : ZMod 26549637637)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2212469803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2212469803, 1)] : List FactorBlock).map factorBlockValue).prod) = 26549637637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2212469803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26549637637) ^ 13274818818 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26549637637) ^ 8849879212 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26549637637) ^ 12 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_26896283387 : Nat.Prime 26896283387 := by
  apply lucas_primality 26896283387 (2 : ZMod 26896283387)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (51923327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26896283387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_37
      · exact prime_oneHundredFortyEH_51923327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26896283387) ^ 13448141693 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 3842326198 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 726926578 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26896283387) ^ 518 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_32516260177 : Nat.Prime 32516260177 := by
  apply lucas_primality 32516260177 (10 : ZMod 32516260177)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (193, 1), (1187, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (193, 1), (1187, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) = 32516260177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_193
      · exact prime_oneHundredFortyEH_1187
      · exact prime_oneHundredFortyEH_2957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32516260177) ^ 16258130088 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32516260177) ^ 10838753392 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32516260177) ^ 168478032 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32516260177) ^ 27393648 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 32516260177) ^ 10996368 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_39845729629 : Nat.Prime 39845729629 := by
  apply lucas_primality 39845729629 (2 : ZMod 39845729629)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (40993549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (40993549, 1)] : List FactorBlock).map factorBlockValue).prod) = 39845729629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_40993549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39845729629) ^ 19922864814 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39845729629) ^ 13281909876 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39845729629) ^ 972 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_40611412661 : Nat.Prime 40611412661 := by
  apply lucas_primality 40611412661 (2 : ZMod 40611412661)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 3), (13, 1), (29, 1), (41, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 3), (13, 1), (29, 1), (41, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 40611412661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40611412661) ^ 20305706330 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 8122282532 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 5801630380 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 3123954820 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 1400393540 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 990522260 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40611412661) ^ 106035020 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_43430562811 : Nat.Prime 43430562811 := by
  apply lucas_primality 43430562811 (2 : ZMod 43430562811)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (317, 1), (751, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (317, 1), (751, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 43430562811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_317
      · exact prime_oneHundredFortyEH_751
      · exact prime_oneHundredFortyEH_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43430562811) ^ 21715281405 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43430562811) ^ 14476854270 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43430562811) ^ 8686112562 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43430562811) ^ 137004930 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43430562811) ^ 57830310 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43430562811) ^ 21426030 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_44868075229 : Nat.Prime 44868075229 := by
  apply lucas_primality 44868075229 (2 : ZMod 44868075229)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (173, 1), (587, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (173, 1), (587, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod) = 44868075229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_173
      · exact prime_oneHundredFortyEH_587
      · exact prime_oneHundredFortyEH_4091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44868075229) ^ 22434037614 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 14956025076 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 259353036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 76436244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 10967508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_45721891067 : Nat.Prime 45721891067 := by
  apply lucas_primality 45721891067 (2 : ZMod 45721891067)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22860945533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22860945533, 1)] : List FactorBlock).map factorBlockValue).prod) = 45721891067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_22860945533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45721891067) ^ 22860945533 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45721891067) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_60894924109 : Nat.Prime 60894924109 := by
  apply lucas_primality 60894924109 (2 : ZMod 60894924109)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1213, 1), (181891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1213, 1), (181891, 1)] : List FactorBlock).map factorBlockValue).prod) = 60894924109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_1213
      · exact prime_oneHundredFortyEH_181891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60894924109) ^ 30447462054 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60894924109) ^ 20298308036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60894924109) ^ 2647605396 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60894924109) ^ 50201916 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 60894924109) ^ 334788 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_67283234531 : Nat.Prime 67283234531 := by
  apply lucas_primality 67283234531 (2 : ZMod 67283234531)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (354122287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (354122287, 1)] : List FactorBlock).map factorBlockValue).prod) = 67283234531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_354122287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67283234531) ^ 33641617265 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 13456646906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 3541222870 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 190 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_74775919583 : Nat.Prime 74775919583 := by
  apply lucas_primality 74775919583 (5 : ZMod 74775919583)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (43, 1), (9554807, 1)] : List FactorBlock).map factorBlockValue).prod) = 74775919583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_9554807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74775919583) ^ 37387959791 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 10682274226 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 5751993814 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 1738974874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 74775919583) ^ 7826 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_82458253063 : Nat.Prime 82458253063 := by
  apply lucas_primality 82458253063 (3 : ZMod 82458253063)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3557, 1), (1287887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3557, 1), (1287887, 1)] : List FactorBlock).map factorBlockValue).prod) = 82458253063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_3557
      · exact prime_oneHundredFortyEH_1287887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82458253063) ^ 41229126531 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82458253063) ^ 27486084354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82458253063) ^ 23181966 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82458253063) ^ 64026 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_90385817857 : Nat.Prime 90385817857 := by
  apply lucas_primality 90385817857 (15 : ZMod 90385817857)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (117689867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (117689867, 1)] : List FactorBlock).map factorBlockValue).prod) = 90385817857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_117689867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 90385817857) ^ 45192908928 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (15 : ZMod 90385817857) ^ 30128605952 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (15 : ZMod 90385817857) ^ 768 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_97571497217 : Nat.Prime 97571497217 := by
  apply lucas_primality 97571497217 (3 : ZMod 97571497217)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (381138661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (381138661, 1)] : List FactorBlock).map factorBlockValue).prod) = 97571497217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_381138661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 97571497217) ^ 48785748608 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 97571497217) ^ 256 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_105307914797 : Nat.Prime 105307914797 := by
  apply lucas_primality 105307914797 (3 : ZMod 105307914797)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3760996957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3760996957, 1)] : List FactorBlock).map factorBlockValue).prod) = 105307914797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_3760996957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 105307914797) ^ 52653957398 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 105307914797) ^ 15043987828 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 105307914797) ^ 28 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_108177844891 : Nat.Prime 108177844891 := by
  apply lucas_primality 108177844891 (2 : ZMod 108177844891)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (38959, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (38959, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) = 108177844891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_38959
      · exact prime_oneHundredFortyEH_92557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108177844891) ^ 54088922445 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108177844891) ^ 36059281630 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108177844891) ^ 21635568978 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108177844891) ^ 2776710 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108177844891) ^ 1168770 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_109736033929 : Nat.Prime 109736033929 := by
  apply lucas_primality 109736033929 (13 : ZMod 109736033929)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) = 109736033929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_3163
      · exact prime_oneHundredFortyEH_1445569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 109736033929) ^ 54868016964 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 36578677976 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 34693656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 75912 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_114530285677 : Nat.Prime 114530285677 := by
  apply lucas_primality 114530285677 (2 : ZMod 114530285677)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (561422969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (561422969, 1)] : List FactorBlock).map factorBlockValue).prod) = 114530285677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_561422969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 114530285677) ^ 57265142838 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 114530285677) ^ 38176761892 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 114530285677) ^ 6737075628 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 114530285677) ^ 204 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_853
      · exact prime_oneHundredFortyEH_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_89
      · exact prime_oneHundredFortyEH_373
      · exact prime_oneHundredFortyEH_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_163063364951 : Nat.Prime 163063364951 := by
  apply lucas_primality 163063364951 (11 : ZMod 163063364951)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (881, 1), (3701779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (881, 1), (3701779, 1)] : List FactorBlock).map factorBlockValue).prod) = 163063364951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_881
      · exact prime_oneHundredFortyEH_3701779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 163063364951) ^ 81531682475 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 163063364951) ^ 32612672990 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 163063364951) ^ 185088950 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 163063364951) ^ 44050 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_195097561063 : Nat.Prime 195097561063 := by
  apply lucas_primality 195097561063 (3 : ZMod 195097561063)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32516260177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32516260177, 1)] : List FactorBlock).map factorBlockValue).prod) = 195097561063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_32516260177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 195097561063) ^ 97548780531 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 195097561063) ^ 65032520354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 195097561063) ^ 6 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_216808939549 : Nat.Prime 216808939549 := by
  apply lucas_primality 216808939549 (6 : ZMod 216808939549)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (137, 1), (14653213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (137, 1), (14653213, 1)] : List FactorBlock).map factorBlockValue).prod) = 216808939549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_137
      · exact prime_oneHundredFortyEH_14653213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 216808939549) ^ 108404469774 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 216808939549) ^ 72269646516 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 216808939549) ^ 1582547004 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 216808939549) ^ 14796 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_269139306067 : Nat.Prime 269139306067 := by
  apply lucas_primality 269139306067 (2 : ZMod 269139306067)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (331, 1), (967, 1), (140143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (331, 1), (967, 1), (140143, 1)] : List FactorBlock).map factorBlockValue).prod) = 269139306067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_331
      · exact prime_oneHundredFortyEH_967
      · exact prime_oneHundredFortyEH_140143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 269139306067) ^ 134569653033 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 269139306067) ^ 89713102022 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 269139306067) ^ 813109686 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 269139306067) ^ 278323998 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 269139306067) ^ 1920462 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_334805801779 : Nat.Prime 334805801779 := by
  apply lucas_primality 334805801779 (2 : ZMod 334805801779)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17579, 1), (151157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17579, 1), (151157, 1)] : List FactorBlock).map factorBlockValue).prod) = 334805801779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17579
      · exact prime_oneHundredFortyEH_151157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 334805801779) ^ 167402900889 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334805801779) ^ 111601933926 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334805801779) ^ 47829400254 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334805801779) ^ 19045782 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 334805801779) ^ 2214954 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_340078141943 : Nat.Prime 340078141943 := by
  apply lucas_primality 340078141943 (5 : ZMod 340078141943)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) = 340078141943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_881
      · exact prime_oneHundredFortyEH_2506583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 340078141943) ^ 170039070971 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 48582591706 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 30916194722 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 386013782 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 135674 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_3931
      · exact prime_oneHundredFortyEH_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_427121300479 : Nat.Prime 427121300479 := by
  apply lucas_primality 427121300479 (3 : ZMod 427121300479)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4211, 1), (16904983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4211, 1), (16904983, 1)] : List FactorBlock).map factorBlockValue).prod) = 427121300479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_4211
      · exact prime_oneHundredFortyEH_16904983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 427121300479) ^ 213560650239 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 427121300479) ^ 142373766826 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 427121300479) ^ 101429898 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 427121300479) ^ 25266 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_446011079209 : Nat.Prime 446011079209 := by
  apply lucas_primality 446011079209 (7 : ZMod 446011079209)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (829, 1), (723133, 1)] : List FactorBlock).map factorBlockValue).prod) = 446011079209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_829
      · exact prime_oneHundredFortyEH_723133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 446011079209) ^ 223005539604 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 148670359736 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 14387454168 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 538010952 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 446011079209) ^ 616776 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_625830854527 : Nat.Prime 625830854527 := by
  apply lucas_primality 625830854527 (3 : ZMod 625830854527)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (17, 1), (29, 1), (431, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (17, 1), (29, 1), (431, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) = 625830854527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_431
      · exact prime_oneHundredFortyEH_18181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 625830854527) ^ 312915427263 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 208610284842 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 36813579678 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 21580374294 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 1452043746 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 34422246 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_649654378099 : Nat.Prime 649654378099 := by
  apply lucas_primality 649654378099 (10 : ZMod 649654378099)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (427967311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (427967311, 1)] : List FactorBlock).map factorBlockValue).prod) = 649654378099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_427967311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 649654378099) ^ 324827189049 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 216551459366 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 59059488918 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 28245842526 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 1518 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_691788953137 : Nat.Prime 691788953137 := by
  apply lucas_primality 691788953137 (10 : ZMod 691788953137)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (351518777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (351518777, 1)] : List FactorBlock).map factorBlockValue).prod) = 691788953137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_351518777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 691788953137) ^ 345894476568 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 230596317712 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 16872901296 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 1968 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_904389307669 : Nat.Prime 904389307669 := by
  apply lucas_primality 904389307669 (2 : ZMod 904389307669)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (347, 1), (313409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (347, 1), (313409, 1)] : List FactorBlock).map factorBlockValue).prod) = 904389307669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_347
      · exact prime_oneHundredFortyEH_313409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 904389307669) ^ 452194653834 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 904389307669) ^ 301463102556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 904389307669) ^ 129198472524 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 904389307669) ^ 82217209788 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 904389307669) ^ 2606309244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 904389307669) ^ 2885652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_945089810869 : Nat.Prime 945089810869 := by
  apply lucas_primality 945089810869 (2 : ZMod 945089810869)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (61, 1), (157, 1), (1174801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (61, 1), (157, 1), (1174801, 1)] : List FactorBlock).map factorBlockValue).prod) = 945089810869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_61
      · exact prime_oneHundredFortyEH_157
      · exact prime_oneHundredFortyEH_1174801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 945089810869) ^ 472544905434 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 945089810869) ^ 315029936956 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 945089810869) ^ 135012830124 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 945089810869) ^ 15493275588 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 945089810869) ^ 6019680324 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 945089810869) ^ 804468 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1022058768707 : Nat.Prime 1022058768707 := by
  apply lucas_primality 1022058768707 (2 : ZMod 1022058768707)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (26896283387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022058768707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_26896283387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1022058768707) ^ 511029384353 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 53792566774 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022058768707) ^ 38 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1030225814899 : Nat.Prime 1030225814899 := by
  apply lucas_primality 1030225814899 (10 : ZMod 1030225814899)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (24529186069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (24529186069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1030225814899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_24529186069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1030225814899) ^ 515112907449 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1030225814899) ^ 343408604966 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1030225814899) ^ 147175116414 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 1030225814899) ^ 42 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1075383918751 : Nat.Prime 1075383918751 := by
  apply lucas_primality 1075383918751 (3 : ZMod 1075383918751)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 5), (67, 1), (211, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 5), (67, 1), (211, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1075383918751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_67
      · exact prime_oneHundredFortyEH_211
      · exact prime_oneHundredFortyEH_4057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1075383918751) ^ 537691959375 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1075383918751) ^ 358461306250 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1075383918751) ^ 215076783750 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1075383918751) ^ 16050506250 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1075383918751) ^ 5096606250 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1075383918751) ^ 265068750 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1623760527167 : Nat.Prime 1623760527167 := by
  apply lucas_primality 1623760527167 (5 : ZMod 1623760527167)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25343, 1), (32035681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25343, 1), (32035681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1623760527167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_25343
      · exact prime_oneHundredFortyEH_32035681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1623760527167) ^ 811880263583 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1623760527167) ^ 64071362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1623760527167) ^ 50686 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1801134966187 : Nat.Prime 1801134966187 := by
  apply lucas_primality 1801134966187 (2 : ZMod 1801134966187)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801134966187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_5886061981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1801134966187) ^ 900567483093 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 600378322062 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 105949115658 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 306 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2147275852489 : Nat.Prime 2147275852489 := by
  apply lucas_primality 2147275852489 (7 : ZMod 2147275852489)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (17, 1), (19, 1), (41, 1), (211, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (17, 1), (19, 1), (41, 1), (211, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2147275852489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_211
      · exact prime_oneHundredFortyEH_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2147275852489) ^ 1073637926244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 715758617496 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 165175065576 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 126310344264 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 113014518552 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 52372581768 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 10176662808 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 2615439528 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2233151512433 : Nat.Prime 2233151512433 := by
  apply lucas_primality 2233151512433 (3 : ZMod 2233151512433)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (7345893133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (7345893133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2233151512433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_7345893133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2233151512433) ^ 1116575756216 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2233151512433) ^ 117534290128 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2233151512433) ^ 304 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2317682119507 : Nat.Prime 2317682119507 := by
  apply lucas_primality 2317682119507 (2 : ZMod 2317682119507)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97, 1), (307, 1), (997813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97, 1), (307, 1), (997813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2317682119507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_97
      · exact prime_oneHundredFortyEH_307
      · exact prime_oneHundredFortyEH_997813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2317682119507) ^ 1158841059753 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 772560706502 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 178283239962 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 23893630098 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 7549453158 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 2322762 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2486991238073 : Nat.Prime 2486991238073 := by
  apply lucas_primality 2486991238073 (3 : ZMod 2486991238073)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2486991238073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_859
      · exact prime_oneHundredFortyEH_1731589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2486991238073) ^ 1243495619036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 226090112552 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 130894275688 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 2895216808 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 1436248 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2598617512397 : Nat.Prime 2598617512397 := by
  apply lucas_primality 2598617512397 (2 : ZMod 2598617512397)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (649654378099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (649654378099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2598617512397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_649654378099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2598617512397) ^ 1299308756198 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2598617512397) ^ 4 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3353735554207 : Nat.Prime 3353735554207 := by
  apply lucas_primality 3353735554207 (3 : ZMod 3353735554207)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3353735554207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_757
      · exact prime_oneHundredFortyEH_25243
      · exact prime_oneHundredFortyEH_29251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3353735554207) ^ 1676867777103 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 1117911851402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 4430297958 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 132858042 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 114653706 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4225626325301 : Nat.Prime 4225626325301 := by
  apply lucas_primality 4225626325301 (2 : ZMod 4225626325301)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (151, 1), (7563319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (151, 1), (7563319, 1)] : List FactorBlock).map factorBlockValue).prod) = 4225626325301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_37
      · exact prime_oneHundredFortyEH_151
      · exact prime_oneHundredFortyEH_7563319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4225626325301) ^ 2112813162650 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4225626325301) ^ 845125265060 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4225626325301) ^ 114206116900 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4225626325301) ^ 27984280300 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4225626325301) ^ 558700 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4466303024867 : Nat.Prime 4466303024867 := by
  apply lucas_primality 4466303024867 (2 : ZMod 4466303024867)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2233151512433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2233151512433, 1)] : List FactorBlock).map factorBlockValue).prod) = 4466303024867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_2233151512433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4466303024867) ^ 2233151512433 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4466303024867) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4870852521719 : Nat.Prime 4870852521719 := by
  apply lucas_primality 4870852521719 (7 : ZMod 4870852521719)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1049, 1), (1499, 1), (26251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1049, 1), (1499, 1), (26251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4870852521719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_59
      · exact prime_oneHundredFortyEH_1049
      · exact prime_oneHundredFortyEH_1499
      · exact prime_oneHundredFortyEH_26251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4870852521719) ^ 2435426260859 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4870852521719) ^ 82556822402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4870852521719) ^ 4643329382 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4870852521719) ^ 3249401282 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 4870852521719) ^ 185549218 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4934642467331 : Nat.Prime 4934642467331 := by
  apply lucas_primality 4934642467331 (2 : ZMod 4934642467331)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) = 4934642467331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_25919
      · exact prime_oneHundredFortyEH_19038707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4934642467331) ^ 2467321233665 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 986928493466 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 190387070 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 259190 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5150564854007 : Nat.Prime 5150564854007 := by
  apply lucas_primality 5150564854007 (5 : ZMod 5150564854007)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (13, 1), (3061, 1), (534851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (13, 1), (3061, 1), (534851, 1)] : List FactorBlock).map factorBlockValue).prod) = 5150564854007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_3061
      · exact prime_oneHundredFortyEH_534851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5150564854007) ^ 2575282427003 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5150564854007) ^ 468233168546 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5150564854007) ^ 396197296462 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5150564854007) ^ 1682641246 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5150564854007) ^ 9629906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5611789596047 : Nat.Prime 5611789596047 := by
  apply lucas_primality 5611789596047 (10 : ZMod 5611789596047)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1879, 1), (64925719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1879, 1), (64925719, 1)] : List FactorBlock).map factorBlockValue).prod) = 5611789596047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_1879
      · exact prime_oneHundredFortyEH_64925719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5611789596047) ^ 2805894798023 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 5611789596047) ^ 243990852002 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 5611789596047) ^ 2986583074 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 5611789596047) ^ 86434 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6206236533649 : Nat.Prime 6206236533649 := by
  apply lucas_primality 6206236533649 (7 : ZMod 6206236533649)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (2791, 1), (15442087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (2791, 1), (15442087, 1)] : List FactorBlock).map factorBlockValue).prod) = 6206236533649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2791
      · exact prime_oneHundredFortyEH_15442087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6206236533649) ^ 3103118266824 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6206236533649) ^ 2068745511216 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6206236533649) ^ 2223660528 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6206236533649) ^ 401904 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6579217434211 : Nat.Prime 6579217434211 := by
  apply lucas_primality 6579217434211 (2 : ZMod 6579217434211)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157, 1), (317, 1), (4406503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157, 1), (317, 1), (4406503, 1)] : List FactorBlock).map factorBlockValue).prod) = 6579217434211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_157
      · exact prime_oneHundredFortyEH_317
      · exact prime_oneHundredFortyEH_4406503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6579217434211) ^ 3289608717105 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579217434211) ^ 2193072478070 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579217434211) ^ 1315843486842 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579217434211) ^ 41905843530 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579217434211) ^ 20754629130 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6579217434211) ^ 1493070 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_8450556055043 : Nat.Prime 8450556055043 := by
  apply lucas_primality 8450556055043 (2 : ZMod 8450556055043)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (83, 1), (2213346269, 1)] : List FactorBlock).map factorBlockValue).prod) = 8450556055043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_83
      · exact prime_oneHundredFortyEH_2213346269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8450556055043) ^ 4225278027521 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 367415480654 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 101813928374 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8450556055043) ^ 3818 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_8524454832463 : Nat.Prime 8524454832463 := by
  apply lucas_primality 8524454832463 (3 : ZMod 8524454832463)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (74775919583, 1)] : List FactorBlock).map factorBlockValue).prod) = 8524454832463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_74775919583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8524454832463) ^ 4262227416231 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 2841484944154 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 448655517498 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8524454832463) ^ 114 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_9566065542823 : Nat.Prime 9566065542823 := by
  apply lucas_primality 9566065542823 (5 : ZMod 9566065542823)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2347, 1), (679311571, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566065542823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2347
      · exact prime_oneHundredFortyEH_679311571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9566065542823) ^ 4783032771411 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 3188688514274 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 4075869426 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9566065542823) ^ 14082 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_10200777472607 : Nat.Prime 10200777472607 := by
  apply lucas_primality 10200777472607 (7 : ZMod 10200777472607)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (31, 1), (59, 1), (439, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (31, 1), (59, 1), (439, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) = 10200777472607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_59
      · exact prime_oneHundredFortyEH_439
      · exact prime_oneHundredFortyEH_6823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10200777472607) ^ 5100388736303 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 1457253924658 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 536883024874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 329057337826 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 172894533434 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 23236395154 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 10200777472607) ^ 1495057522 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_10840810526333 : Nat.Prime 10840810526333 := by
  apply lucas_primality 10840810526333 (2 : ZMod 10840810526333)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (1229, 1), (9464419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (1229, 1), (9464419, 1)] : List FactorBlock).map factorBlockValue).prod) = 10840810526333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_233
      · exact prime_oneHundredFortyEH_1229
      · exact prime_oneHundredFortyEH_9464419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10840810526333) ^ 5420405263166 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10840810526333) ^ 46527083804 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10840810526333) ^ 8820838508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10840810526333) ^ 1145428 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_10981426522441 : Nat.Prime 10981426522441 := by
  apply lucas_primality 10981426522441 (43 : ZMod 10981426522441)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 10981426522441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_103
      · exact prime_oneHundredFortyEH_647
      · exact prime_oneHundredFortyEH_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 10981426522441) ^ 5490713261220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 3660475507480 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2196285304488 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 998311502040 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 354239565240 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 106615791480 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 16972838520 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2726949720 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_12174257517871 : Nat.Prime 12174257517871 := by
  apply lucas_primality 12174257517871 (6 : ZMod 12174257517871)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (222613, 1), (260419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (222613, 1), (260419, 1)] : List FactorBlock).map factorBlockValue).prod) = 12174257517871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_222613
      · exact prime_oneHundredFortyEH_260419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12174257517871) ^ 6087128758935 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12174257517871) ^ 4058085839290 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12174257517871) ^ 2434851503574 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12174257517871) ^ 1739179645410 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12174257517871) ^ 54687990 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12174257517871) ^ 46748730 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_61
      · exact prime_oneHundredFortyEH_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_21232835263921 : Nat.Prime 21232835263921 := by
  apply lucas_primality 21232835263921 (11 : ZMod 21232835263921)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (73, 1), (173131403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (73, 1), (173131403, 1)] : List FactorBlock).map factorBlockValue).prod) = 21232835263921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_73
      · exact prime_oneHundredFortyEH_173131403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 21232835263921) ^ 10616417631960 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 7077611754640 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 4246567052784 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 3033262180560 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 290860757040 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 122640 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_21681621052667 : Nat.Prime 21681621052667 := by
  apply lucas_primality 21681621052667 (2 : ZMod 21681621052667)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10840810526333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10840810526333, 1)] : List FactorBlock).map factorBlockValue).prod) = 21681621052667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_10840810526333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 21681621052667) ^ 10840810526333 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21681621052667) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_23787135054229 : Nat.Prime 23787135054229 := by
  apply lucas_primality 23787135054229 (10 : ZMod 23787135054229)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (17, 1), (107, 1), (11975311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (17, 1), (107, 1), (11975311, 1)] : List FactorBlock).map factorBlockValue).prod) = 23787135054229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_107
      · exact prime_oneHundredFortyEH_11975311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 23787135054229) ^ 11893567527114 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 7929045018076 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 3398162150604 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 1829779619556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 1399243238484 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 222309673404 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 23787135054229) ^ 1986348 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_33699022756921 : Nat.Prime 33699022756921 := by
  apply lucas_primality 33699022756921 (13 : ZMod 33699022756921)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) = 33699022756921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_191
      · exact prime_oneHundredFortyEH_296489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33699022756921) ^ 16849511378460 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 11233007585640 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 6739804551384 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1773632776680 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1162035267480 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 176434674120 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 113660280 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_33980932549547 : Nat.Prime 33980932549547 := by
  apply lucas_primality 33980932549547 (2 : ZMod 33980932549547)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (44171, 1), (384652063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (44171, 1), (384652063, 1)] : List FactorBlock).map factorBlockValue).prod) = 33980932549547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_44171
      · exact prime_oneHundredFortyEH_384652063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33980932549547) ^ 16990466274773 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33980932549547) ^ 769304126 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33980932549547) ^ 88342 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_47111478990451 : Nat.Prime 47111478990451 := by
  apply lucas_primality 47111478990451 (2 : ZMod 47111478990451)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (44868075229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (44868075229, 1)] : List FactorBlock).map factorBlockValue).prod) = 47111478990451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_44868075229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47111478990451) ^ 23555739495225 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 15703826330150 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 9422295798090 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 6730211284350 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 1050 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_53672908848899 : Nat.Prime 53672908848899 := by
  apply lucas_primality 53672908848899 (2 : ZMod 53672908848899)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (101, 1), (227, 1), (617, 1), (46271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (101, 1), (227, 1), (617, 1), (46271, 1)] : List FactorBlock).map factorBlockValue).prod) = 53672908848899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_101
      · exact prime_oneHundredFortyEH_227
      · exact prime_oneHundredFortyEH_617
      · exact prime_oneHundredFortyEH_46271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53672908848899) ^ 26836454424449 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53672908848899) ^ 1309095337778 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53672908848899) ^ 531414939098 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53672908848899) ^ 236444532374 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53672908848899) ^ 86990127794 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53672908848899) ^ 1159968638 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_57793874370247 : Nat.Prime 57793874370247 := by
  apply lucas_primality 57793874370247 (5 : ZMod 57793874370247)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (96697, 1), (279029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57793874370247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_96697
      · exact prime_oneHundredFortyEH_279029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 57793874370247) ^ 28896937185123 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 19264624790082 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 8256267767178 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 3399639668838 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 597680118 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57793874370247) ^ 207124974 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_69397689971923 : Nat.Prime 69397689971923 := by
  apply lucas_primality 69397689971923 (2 : ZMod 69397689971923)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (8783, 1), (101299553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (8783, 1), (101299553, 1)] : List FactorBlock).map factorBlockValue).prod) = 69397689971923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_8783
      · exact prime_oneHundredFortyEH_101299553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69397689971923) ^ 34698844985961 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69397689971923) ^ 23132563323974 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69397689971923) ^ 5338283843994 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69397689971923) ^ 7901365134 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 69397689971923) ^ 685074 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_97417050434381 : Nat.Prime 97417050434381 := by
  apply lucas_primality 97417050434381 (2 : ZMod 97417050434381)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4870852521719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4870852521719, 1)] : List FactorBlock).map factorBlockValue).prod) = 97417050434381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_4870852521719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 97417050434381) ^ 48708525217190 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 97417050434381) ^ 19483410086876 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 97417050434381) ^ 20 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_173
      · exact prime_oneHundredFortyEH_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_139034446677491 : Nat.Prime 139034446677491 := by
  apply lucas_primality 139034446677491 (2 : ZMod 139034446677491)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (19, 1), (443, 1), (18151967, 1)] : List FactorBlock).map factorBlockValue).prod) = 139034446677491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_443
      · exact prime_oneHundredFortyEH_18151967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139034446677491) ^ 69517223338745 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 27806889335498 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 19862063811070 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 10694957436730 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7317602456710 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 313847509430 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 139034446677491) ^ 7659470 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_148781335582813 : Nat.Prime 148781335582813 := by
  apply lucas_primality 148781335582813 (2 : ZMod 148781335582813)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (277, 1), (630418703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (277, 1), (630418703, 1)] : List FactorBlock).map factorBlockValue).prod) = 148781335582813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_277
      · exact prime_oneHundredFortyEH_630418703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148781335582813) ^ 74390667791406 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 49593778527604 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 2095511768772 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 537116734956 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 236004 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_194874783926681 : Nat.Prime 194874783926681 := by
  apply lucas_primality 194874783926681 (3 : ZMod 194874783926681)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (13, 1), (47, 1), (17351, 1), (41777, 1)] : List FactorBlock).map factorBlockValue).prod) = 194874783926681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_47
      · exact prime_oneHundredFortyEH_17351
      · exact prime_oneHundredFortyEH_41777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194874783926681) ^ 97437391963340 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 38974956785336 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 17715889447880 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 14990367994360 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4146271998440 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 11231328680 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 194874783926681) ^ 4664642840 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_197320078064177 : Nat.Prime 197320078064177 := by
  apply lucas_primality 197320078064177 (3 : ZMod 197320078064177)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1327, 1), (4273, 1), (2174941, 1)] : List FactorBlock).map factorBlockValue).prod) = 197320078064177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_1327
      · exact prime_oneHundredFortyEH_4273
      · exact prime_oneHundredFortyEH_2174941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197320078064177) ^ 98660039032088 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 148696366288 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 46178347312 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 197320078064177) ^ 90724336 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_209520105344321 : Nat.Prime 209520105344321 := by
  apply lucas_primality 209520105344321 (3 : ZMod 209520105344321)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (58963, 1), (11104427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (58963, 1), (11104427, 1)] : List FactorBlock).map factorBlockValue).prod) = 209520105344321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_58963
      · exact prime_oneHundredFortyEH_11104427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 209520105344321) ^ 104760052672160 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 41904021068864 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 3553416640 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 18868160 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_220506727127473 : Nat.Prime 220506727127473 := by
  apply lucas_primality 220506727127473 (5 : ZMod 220506727127473)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (53, 1), (9630796957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (53, 1), (9630796957, 1)] : List FactorBlock).map factorBlockValue).prod) = 220506727127473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_53
      · exact prime_oneHundredFortyEH_9630796957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 220506727127473) ^ 110253363563736 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 220506727127473) ^ 73502242375824 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 220506727127473) ^ 4160504285424 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 220506727127473) ^ 22896 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_246387299970467 : Nat.Prime 246387299970467 := by
  apply lucas_primality 246387299970467 (2 : ZMod 246387299970467)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (193, 1), (1014799789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (193, 1), (1014799789, 1)] : List FactorBlock).map factorBlockValue).prod) = 246387299970467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_37
      · exact prime_oneHundredFortyEH_193
      · exact prime_oneHundredFortyEH_1014799789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 246387299970467) ^ 123193649985233 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 246387299970467) ^ 14493370586498 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 246387299970467) ^ 6659116215418 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 246387299970467) ^ 1276618134562 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 246387299970467) ^ 242794 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_10789
      · exact prime_oneHundredFortyEH_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_352856105336047 : Nat.Prime 352856105336047 := by
  apply lucas_primality 352856105336047 (3 : ZMod 352856105336047)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (139, 1), (2503484351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (139, 1), (2503484351, 1)] : List FactorBlock).map factorBlockValue).prod) = 352856105336047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_139
      · exact prime_oneHundredFortyEH_2503484351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 352856105336047) ^ 176428052668023 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 117618701778682 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 27142777333542 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 2538533131914 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 140946 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_382191034750579 : Nat.Prime 382191034750579 := by
  apply lucas_primality 382191034750579 (3 : ZMod 382191034750579)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (21232835263921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (21232835263921, 1)] : List FactorBlock).map factorBlockValue).prod) = 382191034750579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_21232835263921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 382191034750579) ^ 191095517375289 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 382191034750579) ^ 127397011583526 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 382191034750579) ^ 18 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_575627786272421 : Nat.Prime 575627786272421 := by
  apply lucas_primality 575627786272421 (2 : ZMod 575627786272421)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (3083, 1), (1333644841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (3083, 1), (1333644841, 1)] : List FactorBlock).map factorBlockValue).prod) = 575627786272421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_3083
      · exact prime_oneHundredFortyEH_1333644841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 575627786272421) ^ 287813893136210 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 575627786272421) ^ 115125557254484 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 575627786272421) ^ 82232540896060 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 575627786272421) ^ 186710277740 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 575627786272421) ^ 431620 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_701
      · exact prime_oneHundredFortyEH_9769
      · exact prime_oneHundredFortyEH_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_808418374374301 : Nat.Prime 808418374374301 := by
  apply lucas_primality 808418374374301 (6 : ZMod 808418374374301)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) = 808418374374301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_272809
      · exact prime_oneHundredFortyEH_9877709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 808418374374301) ^ 404209187187150 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 269472791458100 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 161683674874860 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 2963312700 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 81842700 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1428108846164981 : Nat.Prime 1428108846164981 := by
  apply lucas_primality 1428108846164981 (3 : ZMod 1428108846164981)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (10200777472607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (10200777472607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1428108846164981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_10200777472607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1428108846164981) ^ 714054423082490 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1428108846164981) ^ 285621769232996 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1428108846164981) ^ 204015549452140 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1428108846164981) ^ 140 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1487813355828131 : Nat.Prime 1487813355828131 := by
  apply lucas_primality 1487813355828131 (2 : ZMod 1487813355828131)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (148781335582813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (148781335582813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1487813355828131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_148781335582813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1487813355828131) ^ 743906677914065 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1487813355828131) ^ 297562671165626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1487813355828131) ^ 10 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1935783595899227 : Nat.Prime 1935783595899227 := by
  apply lucas_primality 1935783595899227 (2 : ZMod 1935783595899227)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23833, 1), (40611412661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23833, 1), (40611412661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1935783595899227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_23833
      · exact prime_oneHundredFortyEH_40611412661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1935783595899227) ^ 967891797949613 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1935783595899227) ^ 81222825322 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1935783595899227) ^ 47666 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4250290743667637 : Nat.Prime 4250290743667637 := by
  apply lucas_primality 4250290743667637 (2 : ZMod 4250290743667637)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (902389, 1), (31824613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (902389, 1), (31824613, 1)] : List FactorBlock).map factorBlockValue).prod) = 4250290743667637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_37
      · exact prime_oneHundredFortyEH_902389
      · exact prime_oneHundredFortyEH_31824613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4250290743667637) ^ 2125145371833818 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 114872722801828 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 4710042724 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 133553572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4716046096484231 : Nat.Prime 4716046096484231 := by
  apply lucas_primality 4716046096484231 (13 : ZMod 4716046096484231)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3691, 1), (3769, 1), (33900637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3691, 1), (3769, 1), (33900637, 1)] : List FactorBlock).map factorBlockValue).prod) = 4716046096484231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_3691
      · exact prime_oneHundredFortyEH_3769
      · exact prime_oneHundredFortyEH_33900637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4716046096484231) ^ 2358023048242115 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4716046096484231) ^ 943209219296846 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4716046096484231) ^ 1277715008530 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4716046096484231) ^ 1251272511670 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 4716046096484231) ^ 139113790 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_5066744382093707 : Nat.Prime 5066744382093707 := by
  apply lucas_primality 5066744382093707 (2 : ZMod 5066744382093707)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (194874783926681, 1)] : List FactorBlock).map factorBlockValue).prod) = 5066744382093707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_194874783926681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5066744382093707) ^ 2533372191046853 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 389749567853362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5066744382093707) ^ 26 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6958272334900987 : Nat.Prime 6958272334900987 := by
  apply lucas_primality 6958272334900987 (2 : ZMod 6958272334900987)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (389, 1), (2737617011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (389, 1), (2737617011, 1)] : List FactorBlock).map factorBlockValue).prod) = 6958272334900987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_389
      · exact prime_oneHundredFortyEH_2737617011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6958272334900987) ^ 3479136167450493 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6958272334900987) ^ 2319424111633662 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6958272334900987) ^ 632570212263726 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6958272334900987) ^ 17887589549874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6958272334900987) ^ 2541726 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_7497228722334083 : Nat.Prime 7497228722334083 := by
  apply lucas_primality 7497228722334083 (2 : ZMod 7497228722334083)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (220506727127473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (220506727127473, 1)] : List FactorBlock).map factorBlockValue).prod) = 7497228722334083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_220506727127473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7497228722334083) ^ 3748614361167041 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7497228722334083) ^ 441013454254946 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7497228722334083) ^ 34 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_8151940739207033 : Nat.Prime 8151940739207033 := by
  apply lucas_primality 8151940739207033 (3 : ZMod 8151940739207033)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (997, 1), (1022058768707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151940739207033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_997
      · exact prime_oneHundredFortyEH_1022058768707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8151940739207033) ^ 4075970369603516 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 8176470149656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8151940739207033) ^ 7976 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_8926880134968787 : Nat.Prime 8926880134968787 := by
  apply lucas_primality 8926880134968787 (2 : ZMod 8926880134968787)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1487813355828131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1487813355828131, 1)] : List FactorBlock).map factorBlockValue).prod) = 8926880134968787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_1487813355828131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8926880134968787) ^ 4463440067484393 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926880134968787) ^ 2975626711656262 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926880134968787) ^ 6 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_9362717398877747 : Nat.Prime 9362717398877747 := by
  apply lucas_primality 9362717398877747 (2 : ZMod 9362717398877747)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (246387299970467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (246387299970467, 1)] : List FactorBlock).map factorBlockValue).prod) = 9362717398877747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_246387299970467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9362717398877747) ^ 4681358699438873 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9362717398877747) ^ 492774599940934 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9362717398877747) ^ 38 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_10402226321133749 : Nat.Prime 10402226321133749 := by
  apply lucas_primality 10402226321133749 (2 : ZMod 10402226321133749)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) = 10402226321133749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_4934642467331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10402226321133749) ^ 5201113160566874 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 611895665949044 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 335555687778508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 2108 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_13334761161373111 : Nat.Prime 13334761161373111 := by
  apply lucas_primality 13334761161373111 (3 : ZMod 13334761161373111)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3881, 1), (114530285677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3881, 1), (114530285677, 1)] : List FactorBlock).map factorBlockValue).prod) = 13334761161373111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_3881
      · exact prime_oneHundredFortyEH_114530285677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13334761161373111) ^ 6667380580686555 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13334761161373111) ^ 4444920387124370 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13334761161373111) ^ 2666952232274622 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13334761161373111) ^ 3435908570310 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13334761161373111) ^ 116430 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_16453308607883281 : Nat.Prime 16453308607883281 := by
  apply lucas_primality 16453308607883281 (17 : ZMod 16453308607883281)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (31, 1), (105307914797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (31, 1), (105307914797, 1)] : List FactorBlock).map factorBlockValue).prod) = 16453308607883281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_105307914797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 16453308607883281) ^ 8226654303941640 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 16453308607883281) ^ 5484436202627760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 16453308607883281) ^ 3290661721576656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 16453308607883281) ^ 2350472658269040 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 16453308607883281) ^ 530751890576880 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 16453308607883281) ^ 156240 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_16695774487261171 : Nat.Prime 16695774487261171 := by
  apply lucas_primality 16695774487261171 (3 : ZMod 16695774487261171)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16695774487261171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_97
      · exact prime_oneHundredFortyEH_167
      · exact prime_oneHundredFortyEH_545326447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16695774487261171) ^ 8347887243630585 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 5565258162420390 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 3339154897452234 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 2385110641037310 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 172121386466610 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 99974697528510 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 30616110 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_18379229417192999 : Nat.Prime 18379229417192999 := by
  apply lucas_primality 18379229417192999 (11 : ZMod 18379229417192999)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) = 18379229417192999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_197
      · exact prime_oneHundredFortyEH_27799
      · exact prime_oneHundredFortyEH_1678038433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 18379229417192999) ^ 9189614708596499 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 93295580797934 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 661147142602 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 10952806 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_23341336425291193 : Nat.Prime 23341336425291193 := by
  apply lucas_primality 23341336425291193 (29 : ZMod 23341336425291193)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (809, 1), (6311, 1), (2473871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (809, 1), (6311, 1), (2473871, 1)] : List FactorBlock).map factorBlockValue).prod) = 23341336425291193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_809
      · exact prime_oneHundredFortyEH_6311
      · exact prime_oneHundredFortyEH_2473871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 23341336425291193) ^ 11670668212645596 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 7780445475097064 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 3334476632184456 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 2121939675026472 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 28852084580088 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 3698516308872 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 23341336425291193) ^ 9435146952 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_28272833852677769 : Nat.Prime 28272833852677769 := by
  apply lucas_primality 28272833852677769 (3 : ZMod 28272833852677769)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (21681621052667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (21681621052667, 1)] : List FactorBlock).map factorBlockValue).prod) = 28272833852677769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_163
      · exact prime_oneHundredFortyEH_21681621052667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28272833852677769) ^ 14136416926338884 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 28272833852677769) ^ 173452968421336 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 28272833852677769) ^ 1304 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_40155521871213053 : Nat.Prime 40155521871213053 := by
  apply lucas_primality 40155521871213053 (2 : ZMod 40155521871213053)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (113, 1), (5813, 1), (355416889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (113, 1), (5813, 1), (355416889, 1)] : List FactorBlock).map factorBlockValue).prod) = 40155521871213053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_113
      · exact prime_oneHundredFortyEH_5813
      · exact prime_oneHundredFortyEH_355416889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40155521871213053) ^ 20077760935606526 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40155521871213053) ^ 933849345842164 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40155521871213053) ^ 355358600630204 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40155521871213053) ^ 6907882654604 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40155521871213053) ^ 112981468 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_44983372334004499 : Nat.Prime 44983372334004499 := by
  apply lucas_primality 44983372334004499 (2 : ZMod 44983372334004499)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7497228722334083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7497228722334083, 1)] : List FactorBlock).map factorBlockValue).prod) = 44983372334004499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7497228722334083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44983372334004499) ^ 22491686167002249 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44983372334004499) ^ 14994457444668166 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44983372334004499) ^ 6 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_53015135238325067 : Nat.Prime 53015135238325067 := by
  apply lucas_primality 53015135238325067 (2 : ZMod 53015135238325067)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (163, 1), (9566065542823, 1)] : List FactorBlock).map factorBlockValue).prod) = 53015135238325067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_163
      · exact prime_oneHundredFortyEH_9566065542823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53015135238325067) ^ 26507567619162533 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 3118537366960298 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 325246228455982 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53015135238325067) ^ 5542 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_145829
      · exact prime_oneHundredFortyEH_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_54505364198768423 : Nat.Prime 54505364198768423 := by
  apply lucas_primality 54505364198768423 (5 : ZMod 54505364198768423)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (139, 1), (8524454832463, 1)] : List FactorBlock).map factorBlockValue).prod) = 54505364198768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_139
      · exact prime_oneHundredFortyEH_8524454832463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54505364198768423) ^ 27252682099384211 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 2369798443424714 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 392124922293298 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 54505364198768423) ^ 6394 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_83230981903196873 : Nat.Prime 83230981903196873 := by
  apply lucas_primality 83230981903196873 (3 : ZMod 83230981903196873)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (11677, 1), (20720264519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (11677, 1), (20720264519, 1)] : List FactorBlock).map factorBlockValue).prod) = 83230981903196873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_11677
      · exact prime_oneHundredFortyEH_20720264519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83230981903196873) ^ 41615490951598436 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 83230981903196873) ^ 1935604230306904 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 83230981903196873) ^ 7127770994536 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 83230981903196873) ^ 4016888 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_113031099583806619 : Nat.Prime 113031099583806619 := by
  apply lucas_primality 113031099583806619 (3 : ZMod 113031099583806619)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (1781089, 1), (207391477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (1781089, 1), (207391477, 1)] : List FactorBlock).map factorBlockValue).prod) = 113031099583806619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_1781089
      · exact prime_oneHundredFortyEH_207391477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113031099583806619) ^ 56515549791903309 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113031099583806619) ^ 37677033194602206 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113031099583806619) ^ 6648888210812154 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113031099583806619) ^ 63461791962 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113031099583806619) ^ 545013234 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_165819169842595471 : Nat.Prime 165819169842595471 := by
  apply lucas_primality 165819169842595471 (12 : ZMod 165819169842595471)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (191, 1), (1009, 1), (3407, 1), (65257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (191, 1), (1009, 1), (3407, 1), (65257, 1)] : List FactorBlock).map factorBlockValue).prod) = 165819169842595471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_191
      · exact prime_oneHundredFortyEH_1009
      · exact prime_oneHundredFortyEH_3407
      · exact prime_oneHundredFortyEH_65257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 165819169842595471) ^ 82909584921297735 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 55273056614198490 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 33163833968519094 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 3856259763781290 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 868163192893170 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 164340108862830 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 48670140840210 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (12 : ZMod 165819169842595471) ^ 2541017359710 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_166461963806393747 : Nat.Prime 166461963806393747 := by
  apply lucas_primality 166461963806393747 (2 : ZMod 166461963806393747)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83230981903196873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83230981903196873, 1)] : List FactorBlock).map factorBlockValue).prod) = 166461963806393747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_83230981903196873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 166461963806393747) ^ 83230981903196873 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 166461963806393747) ^ 2 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_184774819440522523 : Nat.Prime 184774819440522523 := by
  apply lucas_primality 184774819440522523 (3 : ZMod 184774819440522523)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (81816961, 1), (376398767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (81816961, 1), (376398767, 1)] : List FactorBlock).map factorBlockValue).prod) = 184774819440522523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_81816961
      · exact prime_oneHundredFortyEH_376398767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 184774819440522523) ^ 92387409720261261 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184774819440522523) ^ 61591606480174174 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184774819440522523) ^ 2258392602 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184774819440522523) ^ 490901766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_187254347977554941 : Nat.Prime 187254347977554941 := by
  apply lucas_primality 187254347977554941 (2 : ZMod 187254347977554941)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (9362717398877747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (9362717398877747, 1)] : List FactorBlock).map factorBlockValue).prod) = 187254347977554941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_9362717398877747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 187254347977554941) ^ 93627173988777470 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 187254347977554941) ^ 37450869595510988 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 187254347977554941) ^ 20 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_323494058120852441 : Nat.Prime 323494058120852441 := by
  apply lucas_primality 323494058120852441 (3 : ZMod 323494058120852441)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1290319, 1), (6267714769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1290319, 1), (6267714769, 1)] : List FactorBlock).map factorBlockValue).prod) = 323494058120852441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_1290319
      · exact prime_oneHundredFortyEH_6267714769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 323494058120852441) ^ 161747029060426220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 323494058120852441) ^ 64698811624170488 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 323494058120852441) ^ 250708590760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 323494058120852441) ^ 51612760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_338425866592351973 : Nat.Prime 338425866592351973 := by
  apply lucas_primality 338425866592351973 (2 : ZMod 338425866592351973)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (59, 1), (71, 1), (257, 1), (26513, 1), (60493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (59, 1), (71, 1), (257, 1), (26513, 1), (60493, 1)] : List FactorBlock).map factorBlockValue).prod) = 338425866592351973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_59
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_257
      · exact prime_oneHundredFortyEH_26513
      · exact prime_oneHundredFortyEH_60493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338425866592351973) ^ 169212933296175986 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 48346552370335996 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 5736031637158508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 4766561501300732 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 1316832165728996 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 12764525575844 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 338425866592351973) ^ 5594463270004 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_387518401889050781 : Nat.Prime 387518401889050781 := by
  apply lucas_primality 387518401889050781 (7 : ZMod 387518401889050781)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 2), (53672908848899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 2), (53672908848899, 1)] : List FactorBlock).map factorBlockValue).prod) = 387518401889050781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_53672908848899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 387518401889050781) ^ 193759200944525390 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 387518401889050781) ^ 77503680377810156 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 387518401889050781) ^ 20395705362581620 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 387518401889050781) ^ 7220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_565456677053555381 : Nat.Prime 565456677053555381 := by
  apply lucas_primality 565456677053555381 (2 : ZMod 565456677053555381)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (28272833852677769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (28272833852677769, 1)] : List FactorBlock).map factorBlockValue).prod) = 565456677053555381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_28272833852677769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 565456677053555381) ^ 282728338526777690 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 565456677053555381) ^ 113091335410711076 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 565456677053555381) ^ 20 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_685267392948326359 : Nat.Prime 685267392948326359 := by
  apply lucas_primality 685267392948326359 (6 : ZMod 685267392948326359)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (1935783595899227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (1935783595899227, 1)] : List FactorBlock).map factorBlockValue).prod) = 685267392948326359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_59
      · exact prime_oneHundredFortyEH_1935783595899227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 685267392948326359) ^ 342633696474163179 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 685267392948326359) ^ 228422464316108786 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 685267392948326359) ^ 11614701575395362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 685267392948326359) ^ 354 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1530048633721354321 : Nat.Prime 1530048633721354321 := by
  apply lucas_primality 1530048633721354321 (29 : ZMod 1530048633721354321)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (281, 1), (829, 1), (3909625001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (281, 1), (829, 1), (3909625001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530048633721354321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_281
      · exact prime_oneHundredFortyEH_829
      · exact prime_oneHundredFortyEH_3909625001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1530048633721354321) ^ 765024316860677160 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 510016211240451440 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 306009726744270864 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 218578376245907760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 5445012931392720 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 1845655770472080 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (29 : ZMod 1530048633721354321) ^ 391354320 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1574064700918728199 : Nat.Prime 1574064700918728199 := by
  apply lucas_primality 1574064700918728199 (3 : ZMod 1574064700918728199)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2693, 1), (97417050434381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2693, 1), (97417050434381, 1)] : List FactorBlock).map factorBlockValue).prod) = 1574064700918728199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2693
      · exact prime_oneHundredFortyEH_97417050434381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1574064700918728199) ^ 787032350459364099 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574064700918728199) ^ 524688233639576066 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574064700918728199) ^ 584502302606286 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1574064700918728199) ^ 16158 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1799334893360179961 : Nat.Prime 1799334893360179961 := by
  apply lucas_primality 1799334893360179961 (21 : ZMod 1799334893360179961)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (44983372334004499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (44983372334004499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1799334893360179961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_44983372334004499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (21 : ZMod 1799334893360179961) ^ 899667446680089980 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1799334893360179961) ^ 359866978672035992 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (21 : ZMod 1799334893360179961) ^ 40 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2068648210956352507 : Nat.Prime 2068648210956352507 := by
  apply lucas_primality 2068648210956352507 (2 : ZMod 2068648210956352507)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2068648210956352507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_787
      · exact prime_oneHundredFortyEH_33699022756921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2068648210956352507) ^ 1034324105478176253 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 689549403652117502 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 159126785458180962 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 2628523775039838 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 61386 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_101
      · exact prime_oneHundredFortyEH_191
      · exact prime_oneHundredFortyEH_48017
      · exact prime_oneHundredFortyEH_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2775812652630538943 : Nat.Prime 2775812652630538943 := by
  apply lucas_primality 2775812652630538943 (5 : ZMod 2775812652630538943)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (777122653, 1), (1785955307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (777122653, 1), (1785955307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2775812652630538943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_777122653
      · exact prime_oneHundredFortyEH_1785955307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2775812652630538943) ^ 1387906326315269471 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2775812652630538943) ^ 3571910614 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2775812652630538943) ^ 1554245306 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3873419681044591673 : Nat.Prime 3873419681044591673 := by
  apply lucas_primality 3873419681044591673 (3 : ZMod 3873419681044591673)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873419681044591673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_16695774487261171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3873419681044591673) ^ 1936709840522295836 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 133566195898089368 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 232 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_8122220798216447353 : Nat.Prime 8122220798216447353 := by
  apply lucas_primality 8122220798216447353 (10 : ZMod 8122220798216447353)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (338425866592351973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (338425866592351973, 1)] : List FactorBlock).map factorBlockValue).prod) = 8122220798216447353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_338425866592351973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 8122220798216447353) ^ 4061110399108223676 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8122220798216447353) ^ 2707406932738815784 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8122220798216447353) ^ 24 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_11238607983502340953 : Nat.Prime 11238607983502340953 := by
  apply lucas_primality 11238607983502340953 (5 : ZMod 11238607983502340953)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1463117, 1), (45721891067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1463117, 1), (45721891067, 1)] : List FactorBlock).map factorBlockValue).prod) = 11238607983502340953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_1463117
      · exact prime_oneHundredFortyEH_45721891067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11238607983502340953) ^ 5619303991751170476 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11238607983502340953) ^ 3746202661167446984 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11238607983502340953) ^ 1605515426214620136 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11238607983502340953) ^ 7681277699256 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11238607983502340953) ^ 245803656 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_19525163277342448079 : Nat.Prime 19525163277342448079 := by
  apply lucas_primality 19525163277342448079 (7 : ZMod 19525163277342448079)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2789, 1), (1673933, 1), (72107443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2789, 1), (1673933, 1), (72107443, 1)] : List FactorBlock).map factorBlockValue).prod) = 19525163277342448079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_2789
      · exact prime_oneHundredFortyEH_1673933
      · exact prime_oneHundredFortyEH_72107443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19525163277342448079) ^ 9762581638671224039 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19525163277342448079) ^ 673281492322153382 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19525163277342448079) ^ 7000775646232502 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19525163277342448079) ^ 11664244194566 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19525163277342448079) ^ 270778749946 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_49468396905798111733 : Nat.Prime 49468396905798111733 := by
  apply lucas_primality 49468396905798111733 (5 : ZMod 49468396905798111733)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (724277, 1), (334805801779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (724277, 1), (334805801779, 1)] : List FactorBlock).map factorBlockValue).prod) = 49468396905798111733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_724277
      · exact prime_oneHundredFortyEH_334805801779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49468396905798111733) ^ 24734198452899055866 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 49468396905798111733) ^ 16489465635266037244 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 49468396905798111733) ^ 2909905700341065396 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 49468396905798111733) ^ 68300383562916 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 49468396905798111733) ^ 147752508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_52934532249181988737 : Nat.Prime 52934532249181988737 := by
  apply lucas_primality 52934532249181988737 (5 : ZMod 52934532249181988737)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (29, 1), (41, 1), (79, 1), (163063364951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (29, 1), (41, 1), (79, 1), (163063364951, 1)] : List FactorBlock).map factorBlockValue).prod) = 52934532249181988737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_41
      · exact prime_oneHundredFortyEH_79
      · exact prime_oneHundredFortyEH_163063364951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52934532249181988737) ^ 26467266124590994368 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52934532249181988737) ^ 17644844083060662912 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52934532249181988737) ^ 1825328698247654784 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52934532249181988737) ^ 1291086152419072896 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52934532249181988737) ^ 670057370242809984 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52934532249181988737) ^ 324625536 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2063
      · exact prime_oneHundredFortyEH_15269
      · exact prime_oneHundredFortyEH_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_62751102700489265141 : Nat.Prime 62751102700489265141 := by
  apply lucas_primality 62751102700489265141 (2 : ZMod 62751102700489265141)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 3), (1428108846164981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 3), (1428108846164981, 1)] : List FactorBlock).map factorBlockValue).prod) = 62751102700489265141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_1428108846164981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62751102700489265141) ^ 31375551350244632570 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62751102700489265141) ^ 12550220540097853028 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62751102700489265141) ^ 4827007900037635780 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 62751102700489265141) ^ 43940 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_66344737026778446149 : Nat.Prime 66344737026778446149 := by
  apply lucas_primality 66344737026778446149 (3 : ZMod 66344737026778446149)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) = 66344737026778446149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_319053557
      · exact prime_oneHundredFortyEH_4725961831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66344737026778446149) ^ 33172368513389223074 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 6031339729707131468 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 207942320564 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 14038356508 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_85554133689319977371 : Nat.Prime 85554133689319977371 := by
  apply lucas_primality 85554133689319977371 (2 : ZMod 85554133689319977371)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (107, 1), (181, 1), (33980932549547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (107, 1), (181, 1), (33980932549547, 1)] : List FactorBlock).map factorBlockValue).prod) = 85554133689319977371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_107
      · exact prime_oneHundredFortyEH_181
      · exact prime_oneHundredFortyEH_33980932549547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85554133689319977371) ^ 42777066844659988685 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 17110826737863995474 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 6581087206870767490 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 799571342890840910 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 472674771764198770 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85554133689319977371) ^ 2517710 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_87757496123468850851 : Nat.Prime 87757496123468850851 := by
  apply lucas_primality 87757496123468850851 (2 : ZMod 87757496123468850851)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (8377, 1), (209520105344321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (8377, 1), (209520105344321, 1)] : List FactorBlock).map factorBlockValue).prod) = 87757496123468850851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_8377
      · exact prime_oneHundredFortyEH_209520105344321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87757496123468850851) ^ 43878748061734425425 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 17551499224693770170 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 10476005267216050 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 418850 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_94268036096709849533 : Nat.Prime 94268036096709849533 := by
  apply lucas_primality 94268036096709849533 (2 : ZMod 94268036096709849533)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 94268036096709849533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_263
      · exact prime_oneHundredFortyEH_16339
      · exact prime_oneHundredFortyEH_14026408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94268036096709849533) ^ 47134018048354924766 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5545178593924108796 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 4098610265074341284 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 358433597325892964 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5769510747090388 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 6720753548 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_73
      · exact prime_oneHundredFortyEH_79
      · exact prime_oneHundredFortyEH_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_276906115788789989119 : Nat.Prime 276906115788789989119 := by
  apply lucas_primality 276906115788789989119 (3 : ZMod 276906115788789989119)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10333159, 1), (4466303024867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10333159, 1), (4466303024867, 1)] : List FactorBlock).map factorBlockValue).prod) = 276906115788789989119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_10333159
      · exact prime_oneHundredFortyEH_4466303024867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 276906115788789989119) ^ 138453057894394994559 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 276906115788789989119) ^ 92302038596263329706 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 276906115788789989119) ^ 26797818149202 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 276906115788789989119) ^ 61998954 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_293084680029593984827 : Nat.Prime 293084680029593984827 := by
  apply lucas_primality 293084680029593984827 (2 : ZMod 293084680029593984827)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (71, 1), (8647, 1), (1623760527167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (71, 1), (8647, 1), (1623760527167, 1)] : List FactorBlock).map factorBlockValue).prod) = 293084680029593984827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_8647
      · exact prime_oneHundredFortyEH_1623760527167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 293084680029593984827) ^ 146542340014796992413 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 293084680029593984827) ^ 97694893343197994942 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 293084680029593984827) ^ 41869240004227712118 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 293084680029593984827) ^ 4127953239853436406 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 293084680029593984827) ^ 33894377244083958 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 293084680029593984827) ^ 180497478 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_297534392471966499847 : Nat.Prime 297534392471966499847 := by
  apply lucas_primality 297534392471966499847 (33 : ZMod 297534392471966499847)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (48131, 1), (1868173, 1), (183832669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (48131, 1), (1868173, 1), (183832669, 1)] : List FactorBlock).map factorBlockValue).prod) = 297534392471966499847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_48131
      · exact prime_oneHundredFortyEH_1868173
      · exact prime_oneHundredFortyEH_183832669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 297534392471966499847) ^ 148767196235983249923 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 99178130823988833282 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 6181762117387266 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 159264903449502 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 1618506623934 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_377942286057032472047 : Nat.Prime 377942286057032472047 := by
  apply lucas_primality 377942286057032472047 (5 : ZMod 377942286057032472047)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) = 377942286057032472047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_113
      · exact prime_oneHundredFortyEH_199
      · exact prime_oneHundredFortyEH_1592737
      · exact prime_oneHundredFortyEH_5276183617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377942286057032472047) ^ 188971143028516236023 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 3344622000504712142 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 1899207467623278754 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 237291081990958 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 71631753838 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_560360064343831374583 : Nat.Prime 560360064343831374583 := by
  apply lucas_primality 560360064343831374583 (6 : ZMod 560360064343831374583)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (127, 1), (151, 1), (6502439, 1), (249653533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (127, 1), (151, 1), (6502439, 1), (249653533, 1)] : List FactorBlock).map factorBlockValue).prod) = 560360064343831374583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_151
      · exact prime_oneHundredFortyEH_6502439
      · exact prime_oneHundredFortyEH_249653533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 560360064343831374583) ^ 280180032171915687291 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 560360064343831374583) ^ 186786688114610458194 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 560360064343831374583) ^ 4412283971211270666 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 560360064343831374583) ^ 3710993803601532282 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 560360064343831374583) ^ 86176904442138 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 560360064343831374583) ^ 2244550908654 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_695450024211916627019 : Nat.Prime 695450024211916627019 := by
  apply lucas_primality 695450024211916627019 (2 : ZMod 695450024211916627019)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2500999, 1), (139034446677491, 1)] : List FactorBlock).map factorBlockValue).prod) = 695450024211916627019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_2500999
      · exact prime_oneHundredFortyEH_139034446677491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695450024211916627019) ^ 347725012105958313509 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 278068893354982 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 695450024211916627019) ^ 5001998 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_818253362794063446907 : Nat.Prime 818253362794063446907 := by
  apply lucas_primality 818253362794063446907 (2 : ZMod 818253362794063446907)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (313, 1), (13933, 1), (1079879, 1), (1524119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (313, 1), (13933, 1), (1079879, 1), (1524119, 1)] : List FactorBlock).map factorBlockValue).prod) = 818253362794063446907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_313
      · exact prime_oneHundredFortyEH_13933
      · exact prime_oneHundredFortyEH_1079879
      · exact prime_oneHundredFortyEH_1524119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 818253362794063446907) ^ 409126681397031723453 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 272751120931354482302 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 43065966462845444574 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 2614227996147167562 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 58727722873326882 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 757726896063414 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 536869734445974 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_935333422315717534231 : Nat.Prime 935333422315717534231 := by
  apply lucas_primality 935333422315717534231 (17 : ZMod 935333422315717534231)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (601, 1), (4716046096484231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (601, 1), (4716046096484231, 1)] : List FactorBlock).map factorBlockValue).prod) = 935333422315717534231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_601
      · exact prime_oneHundredFortyEH_4716046096484231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 935333422315717534231) ^ 467666711157858767115 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 935333422315717534231) ^ 311777807438572511410 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 935333422315717534231) ^ 187066684463143506846 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 935333422315717534231) ^ 85030311119610684930 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 935333422315717534231) ^ 1556295211839796230 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (17 : ZMod 935333422315717534231) ^ 198330 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_71
      · exact prime_oneHundredFortyEH_199
      · exact prime_oneHundredFortyEH_52864081
      · exact prime_oneHundredFortyEH_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1296492971186983284073 : Nat.Prime 1296492971186983284073 := by
  apply lucas_primality 1296492971186983284073 (5 : ZMod 1296492971186983284073)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (92296627, 1), (195097561063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (92296627, 1), (195097561063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296492971186983284073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_92296627
      · exact prime_oneHundredFortyEH_195097561063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1296492971186983284073) ^ 648246485593491642036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1296492971186983284073) ^ 432164323728994428024 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1296492971186983284073) ^ 14047024396536 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1296492971186983284073) ^ 6645357144 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_2678916134158785731359 : Nat.Prime 2678916134158785731359 := by
  apply lucas_primality 2678916134158785731359 (3 : ZMod 2678916134158785731359)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7867, 1), (87257, 1), (216808939549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7867, 1), (87257, 1), (216808939549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2678916134158785731359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7867
      · exact prime_oneHundredFortyEH_87257
      · exact prime_oneHundredFortyEH_216808939549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2678916134158785731359) ^ 1339458067079392865679 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2678916134158785731359) ^ 892972044719595243786 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2678916134158785731359) ^ 340525757488087674 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2678916134158785731359) ^ 30701446693775694 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2678916134158785731359) ^ 12356114742 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3053393917893592837301 : Nat.Prime 3053393917893592837301 := by
  apply lucas_primality 3053393917893592837301 (2 : ZMod 3053393917893592837301)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (2775812652630538943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (2775812652630538943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3053393917893592837301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_2775812652630538943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3053393917893592837301) ^ 1526696958946796418650 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 610678783578718567460 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 277581265263053894300 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 1100 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3065886316050812130167 : Nat.Prime 3065886316050812130167 := by
  apply lucas_primality 3065886316050812130167 (5 : ZMod 3065886316050812130167)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2237, 1), (685267392948326359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2237, 1), (685267392948326359, 1)] : List FactorBlock).map factorBlockValue).prod) = 3065886316050812130167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_2237
      · exact prime_oneHundredFortyEH_685267392948326359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3065886316050812130167) ^ 1532943158025406065083 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3065886316050812130167) ^ 1370534785896652718 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3065886316050812130167) ^ 4474 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_3122694448544830638701 : Nat.Prime 3122694448544830638701 := by
  apply lucas_primality 3122694448544830638701 (2 : ZMod 3122694448544830638701)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 2), (184774819440522523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 2), (184774819440522523, 1)] : List FactorBlock).map factorBlockValue).prod) = 3122694448544830638701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_184774819440522523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3122694448544830638701) ^ 1561347224272415319350 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122694448544830638701) ^ 624538889708966127740 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122694448544830638701) ^ 240207265272679279900 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3122694448544830638701) ^ 16900 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_9803875754057824351433 : Nat.Prime 9803875754057824351433 := by
  apply lucas_primality 9803875754057824351433 (3 : ZMod 9803875754057824351433)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9803875754057824351433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_13
      · exact prime_oneHundredFortyEH_94268036096709849533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9803875754057824351433) ^ 4901937877028912175716 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 754144288773678796264 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 104 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_20429914326100191595409 : Nat.Prime 20429914326100191595409 := by
  apply lucas_primality 20429914326100191595409 (3 : ZMod 20429914326100191595409)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (23, 1), (193, 1), (32976283, 1), (792988759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (23, 1), (193, 1), (32976283, 1), (792988759, 1)] : List FactorBlock).map factorBlockValue).prod) = 20429914326100191595409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_193
      · exact prime_oneHundredFortyEH_32976283
      · exact prime_oneHundredFortyEH_792988759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20429914326100191595409) ^ 10214957163050095797704 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20429914326100191595409) ^ 1857264938736381054128 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20429914326100191595409) ^ 888257144613051808496 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20429914326100191595409) ^ 105854478373576122256 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20429914326100191595409) ^ 619533569811376 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20429914326100191595409) ^ 25763182761712 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_30491009186022460738717 : Nat.Prime 30491009186022460738717 := by
  apply lucas_primality 30491009186022460738717 (2 : ZMod 30491009186022460738717)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8369, 1), (294703, 1), (1030225814899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8369, 1), (294703, 1), (1030225814899, 1)] : List FactorBlock).map factorBlockValue).prod) = 30491009186022460738717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_8369
      · exact prime_oneHundredFortyEH_294703
      · exact prime_oneHundredFortyEH_1030225814899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30491009186022460738717) ^ 15245504593011230369358 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30491009186022460738717) ^ 10163669728674153579572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30491009186022460738717) ^ 3643327659938159964 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30491009186022460738717) ^ 103463518138676772 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30491009186022460738717) ^ 29596432884 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_39453629037111872997811 : Nat.Prime 39453629037111872997811 := by
  apply lucas_primality 39453629037111872997811 (2 : ZMod 39453629037111872997811)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (89, 1), (552677, 1), (39845729629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (89, 1), (552677, 1), (39845729629, 1)] : List FactorBlock).map factorBlockValue).prod) = 39453629037111872997811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_61
      · exact prime_oneHundredFortyEH_89
      · exact prime_oneHundredFortyEH_552677
      · exact prime_oneHundredFortyEH_39845729629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39453629037111872997811) ^ 19726814518555936498905 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 13151209679037290999270 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 7890725807422374599562 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 3586693548828352090710 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 646780803887079885210 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 443299202664178348290 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 71386413831427530 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39453629037111872997811) ^ 990159532890 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_94954930555009359595661 : Nat.Prime 94954930555009359595661 := by
  apply lucas_primality 94954930555009359595661 (2 : ZMod 94954930555009359595661)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) = 94954930555009359595661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_1621
      · exact prime_oneHundredFortyEH_3623
      · exact prime_oneHundredFortyEH_808418374374301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94954930555009359595661) ^ 47477465277504679797830 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 18990986111001871919132 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 58577995407161850460 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 26208923697214838420 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 117457660 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_102603667664945300223157 : Nat.Prime 102603667664945300223157 := by
  apply lucas_primality 102603667664945300223157 (2 : ZMod 102603667664945300223157)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2011699, 1), (4250290743667637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2011699, 1), (4250290743667637, 1)] : List FactorBlock).map factorBlockValue).prod) = 102603667664945300223157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2011699
      · exact prime_oneHundredFortyEH_4250290743667637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102603667664945300223157) ^ 51301833832472650111578 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 34201222554981766741052 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 51003488924011644 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 24140388 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_113063251244859843498343 : Nat.Prime 113063251244859843498343 := by
  apply lucas_primality 113063251244859843498343 (3 : ZMod 113063251244859843498343)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (523, 1), (1861583, 1), (26549637637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (523, 1), (1861583, 1), (26549637637, 1)] : List FactorBlock).map factorBlockValue).prod) = 113063251244859843498343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_523
      · exact prime_oneHundredFortyEH_1861583
      · exact prime_oneHundredFortyEH_26549637637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113063251244859843498343) ^ 56531625622429921749171 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 37687750414953281166114 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 216182124751166048754 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 60735004157676474 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 4258560993966 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_152115249699610919765639 : Nat.Prime 152115249699610919765639 := by
  apply lucas_primality 152115249699610919765639 (7 : ZMod 152115249699610919765639)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (127, 1), (85554133689319977371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (127, 1), (85554133689319977371, 1)] : List FactorBlock).map factorBlockValue).prod) = 152115249699610919765639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_85554133689319977371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 152115249699610919765639) ^ 76057624849805459882819 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 21730749957087274252234 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 1197757871650479683194 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 152115249699610919765639) ^ 1778 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_171040430309519845172041 : Nat.Prime 171040430309519845172041 := by
  apply lucas_primality 171040430309519845172041 (7 : ZMod 171040430309519845172041)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (73, 1), (19525163277342448079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (73, 1), (19525163277342448079, 1)] : List FactorBlock).map factorBlockValue).prod) = 171040430309519845172041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_73
      · exact prime_oneHundredFortyEH_19525163277342448079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 171040430309519845172041) ^ 85520215154759922586020 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 171040430309519845172041) ^ 57013476769839948390680 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 171040430309519845172041) ^ 34208086061903969034408 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 171040430309519845172041) ^ 2343019593281093769480 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 171040430309519845172041) ^ 8760 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_452253004979439373993373 : Nat.Prime 452253004979439373993373 := by
  apply lucas_primality 452253004979439373993373 (2 : ZMod 452253004979439373993373)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113063251244859843498343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113063251244859843498343, 1)] : List FactorBlock).map factorBlockValue).prod) = 452253004979439373993373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_113063251244859843498343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 452253004979439373993373) ^ 226126502489719686996686 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 452253004979439373993373) ^ 4 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_513863111834671844657597 : Nat.Prime 513863111834671844657597 := by
  apply lucas_primality 513863111834671844657597 (2 : ZMod 513863111834671844657597)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (818253362794063446907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (818253362794063446907, 1)] : List FactorBlock).map factorBlockValue).prod) = 513863111834671844657597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_157
      · exact prime_oneHundredFortyEH_818253362794063446907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 513863111834671844657597) ^ 256931555917335922328798 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 513863111834671844657597) ^ 3273013451176253787628 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 513863111834671844657597) ^ 628 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_594451756678872203951309 : Nat.Prime 594451756678872203951309 := by
  apply lucas_primality 594451756678872203951309 (2 : ZMod 594451756678872203951309)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37991, 1), (488478559, 1), (1144016669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37991, 1), (488478559, 1), (1144016669, 1)] : List FactorBlock).map factorBlockValue).prod) = 594451756678872203951309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_37991
      · exact prime_oneHundredFortyEH_488478559
      · exact prime_oneHundredFortyEH_1144016669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 594451756678872203951309) ^ 297225878339436101975654 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 594451756678872203951309) ^ 84921679525553171993044 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 594451756678872203951309) ^ 15647173190462799188 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 594451756678872203951309) ^ 1216945443615412 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 594451756678872203951309) ^ 519618090179132 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1506524832519274576092827 : Nat.Prime 1506524832519274576092827 := by
  apply lucas_primality 1506524832519274576092827 (2 : ZMod 1506524832519274576092827)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (1296492971186983284073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (1296492971186983284073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1506524832519274576092827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_83
      · exact prime_oneHundredFortyEH_1296492971186983284073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1506524832519274576092827) ^ 753262416259637288046413 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506524832519274576092827) ^ 215217833217039225156118 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506524832519274576092827) ^ 18150901596617765977022 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506524832519274576092827) ^ 1162 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1650733165528679251329829 : Nat.Prime 1650733165528679251329829 := by
  apply lucas_primality 1650733165528679251329829 (2 : ZMod 1650733165528679251329829)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (283, 1), (331, 1), (3023, 1), (69397689971923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (283, 1), (331, 1), (3023, 1), (69397689971923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650733165528679251329829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_283
      · exact prime_oneHundredFortyEH_331
      · exact prime_oneHundredFortyEH_3023
      · exact prime_oneHundredFortyEH_69397689971923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1650733165528679251329829) ^ 825366582764339625664914 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 550244388509559750443276 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 235819023646954178761404 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 5832979383493566259116 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 4987109261415949399788 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 546057944270155227036 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1650733165528679251329829) ^ 23786572236 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_1845788183448698491759957 : Nat.Prime 1845788183448698491759957 := by
  apply lucas_primality 1845788183448698491759957 (2 : ZMod 1845788183448698491759957)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (673, 1), (1373, 1), (166461963806393747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (673, 1), (1373, 1), (166461963806393747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1845788183448698491759957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_673
      · exact prime_oneHundredFortyEH_1373
      · exact prime_oneHundredFortyEH_166461963806393747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1845788183448698491759957) ^ 922894091724349245879978 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845788183448698491759957) ^ 615262727816232830586652 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845788183448698491759957) ^ 2742627315674143375572 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845788183448698491759957) ^ 1344346819700435900772 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845788183448698491759957) ^ 11088348 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4207034638293855065744621 : Nat.Prime 4207034638293855065744621 := by
  apply lucas_primality 4207034638293855065744621 (3 : ZMod 4207034638293855065744621)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (25889, 1), (165819169842595471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (25889, 1), (165819169842595471, 1)] : List FactorBlock).map factorBlockValue).prod) = 4207034638293855065744621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_25889
      · exact prime_oneHundredFortyEH_165819169842595471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4207034638293855065744621) ^ 2103517319146927532872310 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4207034638293855065744621) ^ 841406927658771013148924 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4207034638293855065744621) ^ 601004948327693580820660 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4207034638293855065744621) ^ 162502786445743561580 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4207034638293855065744621) ^ 25371220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_97
      · exact prime_oneHundredFortyEH_719
      · exact prime_oneHundredFortyEH_17207
      · exact prime_oneHundredFortyEH_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6629445418928791598974271 : Nat.Prime 6629445418928791598974271 := by
  apply lucas_primality 6629445418928791598974271 (13 : ZMod 6629445418928791598974271)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (20113, 1), (723639199, 1), (2397312559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (20113, 1), (723639199, 1), (2397312559, 1)] : List FactorBlock).map factorBlockValue).prod) = 6629445418928791598974271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_20113
      · exact prime_oneHundredFortyEH_723639199
      · exact prime_oneHundredFortyEH_2397312559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6629445418928791598974271) ^ 3314722709464395799487135 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6629445418928791598974271) ^ 1325889083785758319794854 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6629445418928791598974271) ^ 348918179943620610472330 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6629445418928791598974271) ^ 329609974590006045790 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6629445418928791598974271) ^ 9161258024841730 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6629445418928791598974271) ^ 2765365489802530 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_6861676634375057617593509 : Nat.Prime 6861676634375057617593509 := by
  apply lucas_primality 6861676634375057617593509 (2 : ZMod 6861676634375057617593509)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (210430769, 1), (8151940739207033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6861676634375057617593509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_210430769
      · exact prime_oneHundredFortyEH_8151940739207033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6861676634375057617593509) ^ 3430838317187528808796754 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 32607762956828132 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6861676634375057617593509) ^ 841723076 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_10954160408629724675816719 : Nat.Prime 10954160408629724675816719 := by
  apply lucas_primality 10954160408629724675816719 (3 : ZMod 10954160408629724675816719)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) = 10954160408629724675816719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_16787
      · exact prime_oneHundredFortyEH_857453
      · exact prime_oneHundredFortyEH_2486991238073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10954160408629724675816719) ^ 5477080204314862337908359 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 3651386802876574891938906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 644362376978219098577454 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 652538298006178869114 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 12775231305540624006 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 4404583434366 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_12882733793150306650964401 : Nat.Prime 12882733793150306650964401 := by
  apply lucas_primality 12882733793150306650964401 (13 : ZMod 12882733793150306650964401)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (2459, 1), (64887553, 1), (67283234531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (2459, 1), (64887553, 1), (67283234531, 1)] : List FactorBlock).map factorBlockValue).prod) = 12882733793150306650964401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_2459
      · exact prime_oneHundredFortyEH_64887553
      · exact prime_oneHundredFortyEH_67283234531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12882733793150306650964401) ^ 6441366896575153325482200 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 4294244597716768883654800 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 2576546758630061330192880 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 5239013335970031171600 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 198539368454074800 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 191470191392400 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_23922151145309313463158061 : Nat.Prime 23922151145309313463158061 := by
  apply lucas_primality 23922151145309313463158061 (2 : ZMod 23922151145309313463158061)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (23, 1), (31, 1), (179, 1), (241, 1), (5233, 1), (18624601987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (19, 1), (23, 1), (31, 1), (179, 1), (241, 1), (5233, 1), (18624601987, 1)] : List FactorBlock).map factorBlockValue).prod) = 23922151145309313463158061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_19
      · exact prime_oneHundredFortyEH_23
      · exact prime_oneHundredFortyEH_31
      · exact prime_oneHundredFortyEH_179
      · exact prime_oneHundredFortyEH_241
      · exact prime_oneHundredFortyEH_5233
      · exact prime_oneHundredFortyEH_18624601987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23922151145309313463158061) ^ 11961075572654656731579030 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 7974050381769771154386020 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 4784430229061862692631612 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 3417450163615616209022580 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 1259060586595227024376740 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 1040093528056926672311220 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 771682295009977853650260 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 133643302487761527727140 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 99262037947341549639660 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 4571402855973497699820 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23922151145309313463158061) ^ 1284438247969380 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_73792850545873892042617309 : Nat.Prime 73792850545873892042617309 := by
  apply lucas_primality 73792850545873892042617309 (6 : ZMod 73792850545873892042617309)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (43, 1), (20429914326100191595409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (43, 1), (20429914326100191595409, 1)] : List FactorBlock).map factorBlockValue).prod) = 73792850545873892042617309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_43
      · exact prime_oneHundredFortyEH_20429914326100191595409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73792850545873892042617309) ^ 36896425272936946021308654 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 73792850545873892042617309) ^ 24597616848624630680872436 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 73792850545873892042617309) ^ 10541835792267698863231044 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 73792850545873892042617309) ^ 1716112803392416094014356 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (6 : ZMod 73792850545873892042617309) ^ 3612 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_316476794979723020748739243 : Nat.Prime 316476794979723020748739243 := by
  apply lucas_primality 316476794979723020748739243 (2 : ZMod 316476794979723020748739243)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (17, 1), (113, 1), (560360064343831374583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (17, 1), (113, 1), (560360064343831374583, 1)] : List FactorBlock).map factorBlockValue).prod) = 316476794979723020748739243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_7
      · exact prime_oneHundredFortyEH_17
      · exact prime_oneHundredFortyEH_113
      · exact prime_oneHundredFortyEH_560360064343831374583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 316476794979723020748739243) ^ 158238397489861510374369621 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 316476794979723020748739243) ^ 105492264993241006916246414 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 316476794979723020748739243) ^ 45210970711389002964105606 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 316476794979723020748739243) ^ 18616282057630765926396426 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 316476794979723020748739243) ^ 2800679601590469210165834 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 316476794979723020748739243) ^ 564774 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_506169308178578409332081419 : Nat.Prime 506169308178578409332081419 := by
  apply lucas_primality 506169308178578409332081419 (3 : ZMod 506169308178578409332081419)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2953, 1), (29437, 1), (323494058120852441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2953, 1), (29437, 1), (323494058120852441, 1)] : List FactorBlock).map factorBlockValue).prod) = 506169308178578409332081419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_2953
      · exact prime_oneHundredFortyEH_29437
      · exact prime_oneHundredFortyEH_323494058120852441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 506169308178578409332081419) ^ 253084654089289204666040709 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 506169308178578409332081419) ^ 168723102726192803110693806 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 506169308178578409332081419) ^ 171408502600263599502906 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 506169308178578409332081419) ^ 17195003165355790648914 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 506169308178578409332081419) ^ 1564694298 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_811359626345074214958777569 : Nat.Prime 811359626345074214958777569 := by
  apply lucas_primality 811359626345074214958777569 (3 : ZMod 811359626345074214958777569)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (61, 1), (127, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (61, 1), (127, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) = 811359626345074214958777569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_61
      · exact prime_oneHundredFortyEH_127
      · exact prime_oneHundredFortyEH_297534392471966499847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 811359626345074214958777569) ^ 405679813172537107479388784 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 73759966031370383178070688 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 13300977481066790409160288 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 6388658475158064684714784 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 2726944 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_909436064694478790393355077 : Nat.Prime 909436064694478790393355077 := by
  apply lucas_primality 909436064694478790393355077 (2 : ZMod 909436064694478790393355077)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4171314503, 1), (54505364198768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 909436064694478790393355077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_4171314503
      · exact prime_oneHundredFortyEH_54505364198768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 909436064694478790393355077) ^ 454718032347239395196677538 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 218021456795073692 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 909436064694478790393355077) ^ 16685258012 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_20689670471799392481448828003 : Nat.Prime 20689670471799392481448828003 := by
  apply lucas_primality 20689670471799392481448828003 (2 : ZMod 20689670471799392481448828003)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) = 20689670471799392481448828003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_29
      · exact prime_oneHundredFortyEH_2663
      · exact prime_oneHundredFortyEH_31033
      · exact prime_oneHundredFortyEH_746371
      · exact prime_oneHundredFortyEH_792107
      · exact prime_oneHundredFortyEH_2433721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20689670471799392481448828003) ^ 10344835235899696240724414001 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 6896556823933130827149609334 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 713436912820668706256856138 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 7769309227112051251013454 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 666699013044159200897394 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 27720356862471066643062 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 26119792492427654952486 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 8501249926264922101362 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_23645337682056448550227232011 : Nat.Prime 23645337682056448550227232011 := by
  apply lucas_primality 23645337682056448550227232011 (3 : ZMod 23645337682056448550227232011)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056448550227232011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_5
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_461
      · exact prime_oneHundredFortyEH_69997
      · exact prime_oneHundredFortyEH_2220502305087140441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056448550227232011) ^ 11822668841028224275113616005 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 7881779227352149516742410670 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 4729067536411289710045446402 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 2149576152914222595475202910 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 51291404950230907918063410 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 337805015672906675289330 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056448550227232011) ^ 10648643610 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_82758681887197569925795312003 : Nat.Prime 82758681887197569925795312003 := by
  apply lucas_primality 82758681887197569925795312003 (2 : ZMod 82758681887197569925795312003)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 3), (101, 1), (102603667664945300223157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 3), (101, 1), (102603667664945300223157, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758681887197569925795312003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_3
      · exact prime_oneHundredFortyEH_11
      · exact prime_oneHundredFortyEH_101
      · exact prime_oneHundredFortyEH_102603667664945300223157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82758681887197569925795312003) ^ 41379340943598784962897656001 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197569925795312003) ^ 27586227295732523308598437334 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197569925795312003) ^ 7523516535199779084163210182 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197569925795312003) ^ 819392889972253167582131802 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82758681887197569925795312003) ^ 806586 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEH_165517363774395139851590624039 : Nat.Prime 165517363774395139851590624039 := by
  apply lucas_primality 165517363774395139851590624039 (7 : ZMod 165517363774395139851590624039)
  · rw [← oneHundredFortyEHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10427, 1), (28663, 1), (276906115788789989119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10427, 1), (28663, 1), (276906115788789989119, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEH_2
      · exact prime_oneHundredFortyEH_10427
      · exact prime_oneHundredFortyEH_28663
      · exact prime_oneHundredFortyEH_276906115788789989119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 165517363774395139851590624039) ^ 82758681887197569925795312019 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 165517363774395139851590624039) ^ 15873919993708174916235794 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 165517363774395139851590624039) ^ 5774600138659426433087626 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide
    · change (7 : ZMod 165517363774395139851590624039) ^ 597738202 ≠ 1
      rw [← oneHundredFortyEHFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624000 : Nat.totient 165517363774395139851590624000 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 8), (5, 3), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_171401, prime_oneHundredFortyEH_714027719, prime_oneHundredFortyEH_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624001 : Nat.totient 165517363774395139851590624001 = 101737986457863559617959959296 := by
  rw [← show ((([(3, 2), (13, 1), (857, 1), (1650733165528679251329829, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_857, prime_oneHundredFortyEH_1650733165528679251329829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624002 : Nat.totient 165517363774395139851590624002 = 80407590436196099439234842880 := by
  rw [← show ((([(2, 1), (53, 1), (103, 1), (76507, 1), (344237, 1), (575627786272421, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_53, prime_oneHundredFortyEH_103, prime_oneHundredFortyEH_76507, prime_oneHundredFortyEH_344237, prime_oneHundredFortyEH_575627786272421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624003 : Nat.totient 165517363774395139851590624003 = 165513156739756845996524840040 := by
  rw [← show ((([(39343, 1), (4207034638293855065744621, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_39343, prime_oneHundredFortyEH_4207034638293855065744621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624004 : Nat.totient 165517363774395139851590624004 = 49660175149833525308007504000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 3), (101, 1), (102603667664945300223157, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_101, prime_oneHundredFortyEH_102603667664945300223157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624005 : Nat.totient 165517363774395139851590624005 = 131727757729869390795920805888 := by
  rw [← show ((([(5, 1), (193, 1), (2585293, 1), (66344737026778446149, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_193, prime_oneHundredFortyEH_2585293, prime_oneHundredFortyEH_66344737026778446149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624006 : Nat.totient 165517363774395139851590624006 = 82758681887197569925795312002 := by
  rw [← show ((([(2, 1), (82758681887197569925795312003, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_82758681887197569925795312003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624007 : Nat.totient 165517363774395139851590624007 = 92273232353683333560196313088 := by
  rw [← show ((([(3, 1), (7, 3), (47, 1), (313, 1), (55413389, 1), (197320078064177, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_47, prime_oneHundredFortyEH_313, prime_oneHundredFortyEH_55413389, prime_oneHundredFortyEH_197320078064177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624008 : Nat.totient 165517363774395139851590624008 = 77775471656120474362747305984 := by
  rw [← show ((([(2, 3), (17, 1), (677, 1), (691788953137, 1), (2598617512397, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_677, prime_oneHundredFortyEH_691788953137, prime_oneHundredFortyEH_2598617512397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624009 : Nat.totient 165517363774395139851590624009 = 164331728731202470760205460080 := by
  rw [← show ((([(181, 1), (607, 1), (1506524832519274576092827, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_181, prime_oneHundredFortyEH_607, prime_oneHundredFortyEH_1506524832519274576092827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624010 : Nat.totient 165517363774395139851590624010 = 44137963394285820247151809920 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_158265131, prime_oneHundredFortyEH_3873419681044591673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624011 : Nat.totient 165517363774395139851590624011 = 165517363772865091109691424800 := by
  rw [← show ((([(108177844891, 1), (1530048633721354321, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_108177844891, prime_oneHundredFortyEH_1530048633721354321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624012 : Nat.totient 165517363774395139851590624012 = 81952530971887580230965657600 := by
  rw [← show ((([(2, 2), (107, 1), (3889, 1), (7297, 1), (311743, 1), (643781, 1), (67902011, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_107, prime_oneHundredFortyEH_3889, prime_oneHundredFortyEH_7297, prime_oneHundredFortyEH_311743, prime_oneHundredFortyEH_643781, prime_oneHundredFortyEH_67902011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624013 : Nat.totient 165517363774395139851590624013 = 109332570566572936415729586288 := by
  rw [← show ((([(3, 1), (109, 1), (506169308178578409332081419, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_109, prime_oneHundredFortyEH_506169308178578409332081419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624014 : Nat.totient 165517363774395139851590624014 = 65479396658002472908321565472 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (909436064694478790393355077, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_909436064694478790393355077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624015 : Nat.totient 165517363774395139851590624015 = 117288330221547560972559232000 := by
  rw [← show ((([(5, 1), (11, 1), (41, 1), (773, 1), (94954930555009359595661, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_41, prime_oneHundredFortyEH_773, prime_oneHundredFortyEH_94954930555009359595661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624016 : Nat.totient 165517363774395139851590624016 = 53248076059197159212883148800 := by
  rw [← show ((([(2, 4), (3, 1), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_29, prime_oneHundredFortyEH_2663, prime_oneHundredFortyEH_31033, prime_oneHundredFortyEH_746371, prime_oneHundredFortyEH_792107, prime_oneHundredFortyEH_2433721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624017 : Nat.totient 165517363774395139851590624017 = 157757536735418051173385360640 := by
  rw [← show ((([(23, 1), (281, 1), (1097194663, 1), (23341336425291193, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_23, prime_oneHundredFortyEH_281, prime_oneHundredFortyEH_1097194663, prime_oneHundredFortyEH_23341336425291193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624018 : Nat.totient 165517363774395139851590624018 = 77629591751485915100458920960 := by
  rw [← show ((([(2, 1), (19, 1), (113, 1), (977, 1), (39453629037111872997811, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_19, prime_oneHundredFortyEH_113, prime_oneHundredFortyEH_977, prime_oneHundredFortyEH_39453629037111872997811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624019 : Nat.totient 165517363774395139851590624019 = 108589436820030610349740074240 := by
  rw [← show ((([(3, 2), (149, 1), (199, 1), (239, 1), (13859, 1), (187254347977554941, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_149, prime_oneHundredFortyEH_199, prime_oneHundredFortyEH_239, prime_oneHundredFortyEH_13859, prime_oneHundredFortyEH_187254347977554941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624020 : Nat.totient 165517363774395139851590624020 = 66206945509332124502815796736 := by
  rw [← show ((([(2, 2), (5, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_155440836073, prime_oneHundredFortyEH_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624021 : Nat.totient 165517363774395139851590624021 = 141872026092020597813866966368 := by
  rw [← show ((([(7, 1), (446011079209, 1), (53015135238325067, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_446011079209, prime_oneHundredFortyEH_53015135238325067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624022 : Nat.totient 165517363774395139851590624022 = 51682509658907714718669081600 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (37, 1), (197, 1), (15031, 1), (8122220798216447353, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_31, prime_oneHundredFortyEH_37, prime_oneHundredFortyEH_197, prime_oneHundredFortyEH_15031, prime_oneHundredFortyEH_8122220798216447353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624023 : Nat.totient 165517363774395139851590624023 = 165517363774388157792120668808 := by
  rw [← show ((([(23787135054229, 1), (6958272334900987, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_23787135054229, prime_oneHundredFortyEH_6958272334900987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624024 : Nat.totient 165517363774395139851590624024 = 82758681887197569925795312008 := by
  rw [← show ((([(2, 3), (20689670471799392481448828003, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_20689670471799392481448828003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624025 : Nat.totient 165517363774395139851590624025 = 82796584347109232347978137600 := by
  rw [← show ((([(3, 1), (5, 2), (17, 1), (331, 1), (3169, 1), (12409, 1), (29327, 1), (340078141943, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_331, prime_oneHundredFortyEH_3169, prime_oneHundredFortyEH_12409, prime_oneHundredFortyEH_29327, prime_oneHundredFortyEH_340078141943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624026 : Nat.totient 165517363774395139851590624026 = 75235165239611710999914343200 := by
  rw [← show ((([(2, 1), (11, 1), (669434911, 1), (11238607983502340953, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_669434911, prime_oneHundredFortyEH_11238607983502340953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624027 : Nat.totient 165517363774395139851590624027 = 152517640883310878317940649600 := by
  rw [← show ((([(13, 1), (571, 1), (3559741, 1), (633960727, 1), (9880600607, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_571, prime_oneHundredFortyEH_3559741, prime_oneHundredFortyEH_633960727, prime_oneHundredFortyEH_9880600607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624028 : Nat.totient 165517363774395139851590624028 = 47290597482586374919730982528 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_607213, prime_oneHundredFortyEH_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624029 : Nat.totient 165517363774395139851590624029 = 165473364538255087530244440576 := by
  rw [← show ((([(3779, 1), (827423, 1), (52934532249181988737, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3779, prime_oneHundredFortyEH_827423, prime_oneHundredFortyEH_52934532249181988737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624030 : Nat.totient 165517363774395139851590624030 = 65218682367177252466866645024 := by
  rw [← show ((([(2, 1), (5, 1), (67, 1), (653647, 1), (377942286057032472047, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_67, prime_oneHundredFortyEH_653647, prime_oneHundredFortyEH_377942286057032472047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624031 : Nat.totient 165517363774395139851590624031 = 110344909181799179685143644160 := by
  rw [← show ((([(3, 1), (97571497217, 1), (565456677053555381, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_97571497217, prime_oneHundredFortyEH_565456677053555381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624032 : Nat.totient 165517363774395139851590624032 = 82751445839117898895811235072 := by
  rw [← show ((([(2, 5), (11437, 1), (452253004979439373993373, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_11437, prime_oneHundredFortyEH_452253004979439373993373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624033 : Nat.totient 165517363774395139851590624033 = 165516769322638460979386394288 := by
  rw [← show ((([(278437, 1), (594451756678872203951309, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_278437, prime_oneHundredFortyEH_594451756678872203951309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624034 : Nat.totient 165517363774395139851590624034 = 54507572828211918807930492240 := by
  rw [← show ((([(2, 1), (3, 1), (83, 1), (355343, 1), (935333422315717534231, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_83, prime_oneHundredFortyEH_355343, prime_oneHundredFortyEH_935333422315717534231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624035 : Nat.totient 165517363774395139851590624035 = 113482609899660887919182472960 := by
  rw [← show ((([(5, 1), (7, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_7561, prime_oneHundredFortyEH_2416168199, prime_oneHundredFortyEH_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624036 : Nat.totient 165517363774395139851590624036 = 82280308003324854508271113632 := by
  rw [← show ((([(2, 2), (173, 1), (625830854527, 1), (382191034750579, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_173, prime_oneHundredFortyEH_625830854527, prime_oneHundredFortyEH_382191034750579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624037 : Nat.totient 165517363774395139851590624037 = 92823698716646831173765768320 := by
  rw [← show ((([(3, 3), (11, 1), (19, 2), (43, 1), (894059, 1), (40155521871213053, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_19, prime_oneHundredFortyEH_43, prime_oneHundredFortyEH_894059, prime_oneHundredFortyEH_40155521871213053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624038 : Nat.totient 165517363774395139851590624038 = 82747857904037501913611809416 := by
  rw [← show ((([(2, 1), (10427, 1), (28663, 1), (276906115788789989119, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_10427, prime_oneHundredFortyEH_28663, prime_oneHundredFortyEH_276906115788789989119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624039 : Nat.totient 165517363774395139851590624039 = 165517363774395139851590624038 := by
  rw [← show ((([(165517363774395139851590624039, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_165517363774395139851590624039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624040 : Nat.totient 165517363774395139851590624040 = 38971312407081665035290894336 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_23, prime_oneHundredFortyEH_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624041 : Nat.totient 165517363774395139851590624041 = 164967955041010746616791928128 := by
  rw [← show ((([(307, 1), (17053, 1), (279709, 1), (113031099583806619, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_307, prime_oneHundredFortyEH_17053, prime_oneHundredFortyEH_279709, prime_oneHundredFortyEH_113031099583806619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624042 : Nat.totient 165517363774395139851590624042 = 66635161851480826130241361920 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (521, 1), (23096547757, 1), (57793874370247, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_521, prime_oneHundredFortyEH_23096547757, prime_oneHundredFortyEH_57793874370247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624043 : Nat.totient 165517363774395139851590624043 = 110344788662806506572192862720 := by
  rw [← show ((([(3, 1), (1817677, 1), (1844813, 1), (16453308607883281, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_1817677, prime_oneHundredFortyEH_1844813, prime_oneHundredFortyEH_16453308607883281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624044 : Nat.totient 165517363774395139851590624044 = 82738025703275020073676902400 := by
  rw [← show ((([(2, 2), (4153, 1), (113537, 1), (87757496123468850851, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_4153, prime_oneHundredFortyEH_113537, prime_oneHundredFortyEH_87757496123468850851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624045 : Nat.totient 165517363774395139851590624045 = 127847894776298770522825840128 := by
  rw [← show ((([(5, 1), (29, 1), (109736033929, 1), (10402226321133749, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_29, prime_oneHundredFortyEH_109736033929, prime_oneHundredFortyEH_10402226321133749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624046 : Nat.totient 165517363774395139851590624046 = 54474039018360205535559902400 := by
  rw [← show ((([(2, 1), (3, 2), (79, 1), (1812773, 1), (2802634271, 1), (22910475971, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_79, prime_oneHundredFortyEH_1812773, prime_oneHundredFortyEH_2802634271, prime_oneHundredFortyEH_22910475971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624047 : Nat.totient 165517363774395139851590624047 = 165410014469022185362778592000 := by
  rw [← show ((([(1543, 1), (2663069, 1), (9532441, 1), (4225626325301, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_1543, prime_oneHundredFortyEH_2663069, prime_oneHundredFortyEH_9532441, prime_oneHundredFortyEH_4225626325301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624048 : Nat.totient 165517363774395139851590624048 = 74204546648545766309554944000 := by
  rw [← show ((([(2, 4), (11, 1), (73, 1), (12882733793150306650964401, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_73, prime_oneHundredFortyEH_12882733793150306650964401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624049 : Nat.totient 165517363774395139851590624049 = 94581342382825503657773403600 := by
  rw [← show ((([(3, 1), (7, 1), (11333351, 1), (695450024211916627019, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_11333351, prime_oneHundredFortyEH_695450024211916627019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624050 : Nat.totient 165517363774395139851590624050 = 64413816634340879866752583680 := by
  rw [← show ((([(2, 1), (5, 2), (59, 2), (97, 1), (9803875754057824351433, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_59, prime_oneHundredFortyEH_97, prime_oneHundredFortyEH_9803875754057824351433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624051 : Nat.totient 165517363774395139851590624051 = 165517363526681187950637332232 := by
  rw [← show ((([(1028939279, 1), (1950831163, 1), (82458253063, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_1028939279, prime_oneHundredFortyEH_1950831163, prime_oneHundredFortyEH_82458253063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624052 : Nat.totient 165517363774395139851590624052 = 55119478930288990164690462720 := by
  rw [← show ((([(2, 2), (3, 1), (1069, 1), (43711, 1), (594023, 1), (5539187, 1), (89710769, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_1069, prime_oneHundredFortyEH_43711, prime_oneHundredFortyEH_594023, prime_oneHundredFortyEH_5539187, prime_oneHundredFortyEH_89710769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624053 : Nat.totient 165517363774395139851590624053 = 147702573762475003223324256000 := by
  rw [← show ((([(13, 2), (31, 1), (1493, 1), (2687, 1), (1403351, 1), (5611789596047, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_31, prime_oneHundredFortyEH_1493, prime_oneHundredFortyEH_2687, prime_oneHundredFortyEH_1403351, prime_oneHundredFortyEH_5611789596047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624054 : Nat.totient 165517363774395139851590624054 = 80995970760380293541387516640 := by
  rw [← show ((([(2, 1), (47, 1), (42899, 1), (43430562811, 1), (945089810869, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_47, prime_oneHundredFortyEH_42899, prime_oneHundredFortyEH_43430562811, prime_oneHundredFortyEH_945089810869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624055 : Nat.totient 165517363774395139851590624055 = 83646875647799839310487552000 := by
  rw [← show ((([(3, 2), (5, 1), (53, 1), (61, 1), (137, 1), (151, 1), (233, 1), (70379, 1), (3353735554207, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_53, prime_oneHundredFortyEH_61, prime_oneHundredFortyEH_137, prime_oneHundredFortyEH_151, prime_oneHundredFortyEH_233, prime_oneHundredFortyEH_70379, prime_oneHundredFortyEH_3353735554207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624056 : Nat.totient 165517363774395139851590624056 = 65398300328610769520697016320 := by
  rw [← show ((([(2, 3), (7, 2), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_19, prime_oneHundredFortyEH_41, prime_oneHundredFortyEH_397, prime_oneHundredFortyEH_13617913, prime_oneHundredFortyEH_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624057 : Nat.totient 165517363774395139851590624057 = 165510734328976211059991624820 := by
  rw [← show ((([(24967, 1), (6629445418928791598974271, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_24967, prime_oneHundredFortyEH_6629445418928791598974271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624058 : Nat.totient 165517363774395139851590624058 = 55172286164225663870255698880 := by
  rw [← show ((([(2, 1), (3, 1), (327581, 1), (16350037229, 1), (5150564854007, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_327581, prime_oneHundredFortyEH_16350037229, prime_oneHundredFortyEH_5150564854007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624059 : Nat.totient 165517363774395139851590624059 = 137791590596981645547790425600 := by
  rw [← show ((([(11, 1), (17, 1), (37, 1), (23922151145309313463158061, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_37, prime_oneHundredFortyEH_23922151145309313463158061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624060 : Nat.totient 165517363774395139851590624060 = 66206943610464788295843111104 := by
  rw [← show ((([(2, 2), (5, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_34858727, prime_oneHundredFortyEH_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624061 : Nat.totient 165517363774395139851590624061 = 108532345186783471315485412800 := by
  rw [← show ((([(3, 1), (71, 1), (421, 1), (1845788183448698491759957, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_71, prime_oneHundredFortyEH_421, prime_oneHundredFortyEH_1845788183448698491759957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624062 : Nat.totient 165517363774395139851590624062 = 81828534259892866857911156800 := by
  rw [← show ((([(2, 1), (89, 1), (297779, 1), (3122694448544830638701, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_89, prime_oneHundredFortyEH_297779, prime_oneHundredFortyEH_3122694448544830638701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624063 : Nat.totient 165517363774395139851590624063 = 135105230284555875088469569152 := by
  rw [← show ((([(7, 1), (23, 1), (227, 1), (235397, 1), (2276699, 1), (8450556055043, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_23, prime_oneHundredFortyEH_227, prime_oneHundredFortyEH_235397, prime_oneHundredFortyEH_2276699, prime_oneHundredFortyEH_8450556055043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624064 : Nat.totient 165517363774395139851590624064 = 55080653500042608677079859200 := by
  rw [← show ((([(2, 6), (3, 4), (601, 1), (24740943389, 1), (2147275852489, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_601, prime_oneHundredFortyEH_24740943389, prime_oneHundredFortyEH_2147275852489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624065 : Nat.totient 165517363774395139851590624065 = 132413891019442587759063862512 := by
  rw [← show ((([(5, 1), (1801134966187, 1), (18379229417192999, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_1801134966187, prime_oneHundredFortyEH_18379229417192999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624066 : Nat.totient 165517363774395139851590624066 = 76363165660866107846131869696 := by
  rw [← show ((([(2, 1), (13, 1), (2593, 1), (37223647, 1), (188752679, 1), (349426349, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_2593, prime_oneHundredFortyEH_37223647, prime_oneHundredFortyEH_188752679, prime_oneHundredFortyEH_349426349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624067 : Nat.totient 165517363774395139851590624067 = 110322888646143102249032143200 := by
  rw [← show ((([(3, 1), (5011, 1), (904389307669, 1), (12174257517871, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5011, prime_oneHundredFortyEH_904389307669, prime_oneHundredFortyEH_12174257517871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624068 : Nat.totient 165517363774395139851590624068 = 82758675780409734138582533600 := by
  rw [← show ((([(2, 2), (13551917, 1), (3053393917893592837301, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_13551917, prime_oneHundredFortyEH_3053393917893592837301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624069 : Nat.totient 165517363774395139851590624069 = 165517192733964830331744484320 := by
  rw [← show ((([(967709, 1), (171040430309519845172041, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_967709, prime_oneHundredFortyEH_171040430309519845172041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624070 : Nat.totient 165517363774395139851590624070 = 34318122479790989678203392000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_461, prime_oneHundredFortyEH_69997, prime_oneHundredFortyEH_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624071 : Nat.totient 165517363774395139851590624071 = 164475088948191716968222546560 := by
  rw [← show ((([(167, 1), (3271, 1), (192497, 1), (1574064700918728199, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_167, prime_oneHundredFortyEH_3271, prime_oneHundredFortyEH_192497, prime_oneHundredFortyEH_1574064700918728199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624072 : Nat.totient 165517363774395139851590624072 = 82758681887161853134526958864 := by
  rw [← show ((([(2, 3), (2317682119507, 1), (8926880134968787, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_2317682119507, prime_oneHundredFortyEH_8926880134968787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624073 : Nat.totient 165517363774395139851590624073 = 110344868183936340270682200000 := by
  rw [← show ((([(3, 2), (2692553, 1), (6351455399, 1), (1075383918751, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_2692553, prime_oneHundredFortyEH_6351455399, prime_oneHundredFortyEH_1075383918751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624074 : Nat.totient 165517363774395139851590624074 = 79904926029543854271863678064 := by
  rw [← show ((([(2, 1), (29, 1), (9736939, 1), (293084680029593984827, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_29, prime_oneHundredFortyEH_9736939, prime_oneHundredFortyEH_293084680029593984827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624075 : Nat.totient 165517363774395139851590624075 = 124153272597696103679600517120 := by
  rw [← show ((([(5, 2), (19, 1), (139, 1), (353, 1), (3433, 1), (2068648210956352507, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_19, prime_oneHundredFortyEH_139, prime_oneHundredFortyEH_353, prime_oneHundredFortyEH_3433, prime_oneHundredFortyEH_2068648210956352507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624076 : Nat.totient 165517363774395139851590624076 = 51927016086084749757361764352 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (811359626345074214958777569, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_811359626345074214958777569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624077 : Nat.totient 165517363774395139851590624077 = 141872026092338691301363392060 := by
  rw [← show ((([(7, 1), (23645337682056448550227232011, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_23645337682056448550227232011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624078 : Nat.totient 165517363774395139851590624078 = 82758681887184228958397405280 := by
  rw [← show ((([(2, 1), (6206236533649, 1), (13334761161373111, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_6206236533649, prime_oneHundredFortyEH_13334761161373111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624079 : Nat.totient 165517363774395139851590624079 = 101836487408850532685740377600 := by
  rw [← show ((([(3, 1), (13, 1), (5821, 1), (36107, 1), (3069133, 1), (6579217434211, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_5821, prime_oneHundredFortyEH_36107, prime_oneHundredFortyEH_3069133, prime_oneHundredFortyEH_6579217434211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624080 : Nat.totient 165517363774395139851590624080 = 64667232023733921551485501440 := by
  rw [← show ((([(2, 4), (5, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_43, prime_oneHundredFortyEH_4282273, prime_oneHundredFortyEH_32701811, prime_oneHundredFortyEH_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624081 : Nat.totient 165517363774395139851590624081 = 149321699886203765410033440000 := by
  rw [← show ((([(11, 1), (131, 1), (63836281, 1), (1799334893360179961, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_131, prime_oneHundredFortyEH_63836281, prime_oneHundredFortyEH_1799334893360179961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624082 : Nat.totient 165517363774395139851590624082 = 55172438517968241664461891480 := by
  rw [← show ((([(2, 1), (3, 2), (3432511, 1), (2678916134158785731359, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_3432511, prime_oneHundredFortyEH_2678916134158785731359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624083 : Nat.totient 165517363774395139851590624083 = 165517333283385953829124456968 := by
  rw [← show ((([(5428399, 1), (30491009186022460738717, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5428399, prime_oneHundredFortyEH_30491009186022460738717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624084 : Nat.totient 165517363774395139851590624084 = 68647735486737664858464353280 := by
  rw [← show ((([(2, 2), (7, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_31, prime_oneHundredFortyEH_3599009, prime_oneHundredFortyEH_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624085 : Nat.totient 165517363774395139851590624085 = 88275767840028284857583616000 := by
  rw [← show ((([(3, 1), (5, 1), (553601, 1), (1815083779, 1), (10981426522441, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_553601, prime_oneHundredFortyEH_1815083779, prime_oneHundredFortyEH_10981426522441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624086 : Nat.totient 165517363774395139851590624086 = 79160117762502973435236709536 := by
  rw [← show ((([(2, 1), (23, 1), (219547, 1), (60894924109, 1), (269139306067, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_23, prime_oneHundredFortyEH_219547, prime_oneHundredFortyEH_60894924109, prime_oneHundredFortyEH_269139306067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624087 : Nat.totient 165517363774395139851590624087 = 165443570923849265959548004536 := by
  rw [← show ((([(2243, 1), (73792850545873892042617309, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2243, prime_oneHundredFortyEH_73792850545873892042617309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624088 : Nat.totient 165517363774395139851590624088 = 55168343686570369242439506560 := by
  rw [← show ((([(2, 3), (3, 1), (13421, 1), (513863111834671844657597, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_13421, prime_oneHundredFortyEH_513863111834671844657597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624089 : Nat.totient 165517363774395139851590624089 = 165200886979415416830841884324 := by
  rw [← show ((([(523, 1), (316476794979723020748739243, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_523, prime_oneHundredFortyEH_316476794979723020748739243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624090 : Nat.totient 165517363774395139851590624090 = 66163128868123537041932976720 := by
  rw [← show ((([(2, 1), (5, 1), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_1511, prime_oneHundredFortyEH_10954160408629724675816719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624091 : Nat.totient 165517363774395139851590624091 = 94487419016471232923107023360 := by
  rw [← show ((([(3, 3), (7, 1), (1223, 1), (8849, 1), (15971, 1), (5066744382093707, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_1223, prime_oneHundredFortyEH_8849, prime_oneHundredFortyEH_15971, prime_oneHundredFortyEH_5066744382093707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624092 : Nat.totient 165517363774395139851590624092 = 69043290899290044600556800000 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (251, 1), (541, 1), (6039193, 1), (352856105336047, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_11, prime_oneHundredFortyEH_13, prime_oneHundredFortyEH_251, prime_oneHundredFortyEH_541, prime_oneHundredFortyEH_6039193, prime_oneHundredFortyEH_352856105336047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624093 : Nat.totient 165517363774395139851590624093 = 155545348734703365196184616960 := by
  rw [← show ((([(17, 1), (661, 1), (10792363, 1), (15099979, 1), (90385817857, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_17, prime_oneHundredFortyEH_661, prime_oneHundredFortyEH_10792363, prime_oneHundredFortyEH_15099979, prime_oneHundredFortyEH_90385817857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624094 : Nat.totient 165517363774395139851590624094 = 52268639411051966080187357472 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (29350187, 1), (49468396905798111733, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_19, prime_oneHundredFortyEH_29350187, prime_oneHundredFortyEH_49468396905798111733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624095 : Nat.totient 165517363774395139851590624095 = 131758578523810188038921260288 := by
  rw [← show ((([(5, 1), (269, 1), (809, 1), (152115249699610919765639, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_269, prime_oneHundredFortyEH_809, prime_oneHundredFortyEH_152115249699610919765639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624096 : Nat.totient 165517363774395139851590624096 = 80507161496892029374992384000 := by
  rw [← show ((([(2, 5), (37, 1), (5441, 1), (545363909, 1), (47111478990451, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_37, prime_oneHundredFortyEH_5441, prime_oneHundredFortyEH_545363909, prime_oneHundredFortyEH_47111478990451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624097 : Nat.totient 165517363774395139851590624097 = 106030612354301286709660944000 := by
  rw [← show ((([(3, 1), (41, 1), (67, 1), (6551, 1), (3065886316050812130167, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_41, prime_oneHundredFortyEH_67, prime_oneHundredFortyEH_6551, prime_oneHundredFortyEH_3065886316050812130167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624098 : Nat.totient 165517363774395139851590624098 = 70894842986363095304976124656 := by
  rw [← show ((([(2, 1), (7, 1), (1723, 1), (6861676634375057617593509, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_7, prime_oneHundredFortyEH_1723, prime_oneHundredFortyEH_6861676634375057617593509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624099 : Nat.totient 165517363774395139851590624099 = 165517363774007621022580272840 := by
  rw [← show ((([(427121300479, 1), (387518401889050781, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_427121300479, prime_oneHundredFortyEH_387518401889050781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624100 : Nat.totient 165517363774395139851590624100 = 44137665771806934583052544000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 2), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_2, prime_oneHundredFortyEH_3, prime_oneHundredFortyEH_5, prime_oneHundredFortyEH_148193, prime_oneHundredFortyEH_732506743, prime_oneHundredFortyEH_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEH_165517363774395139851590624101 : Nat.totient 165517363774395139851590624101 = 161949466534387834550274769600 := by
  rw [← show ((([(47, 1), (5171, 1), (10853, 1), (62751102700489265141, 1)] : List FactorBlock).map factorBlockValue).prod) = 165517363774395139851590624101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEH_47, prime_oneHundredFortyEH_5171, prime_oneHundredFortyEH_10853, prime_oneHundredFortyEH_62751102700489265141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyEH : certifiedKill 1 165517363774395139851590623999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyEH_165517363774395139851590624000, phi_oneHundredFortyEH_165517363774395139851590624001, phi_oneHundredFortyEH_165517363774395139851590624002,
    phi_oneHundredFortyEH_165517363774395139851590624003, phi_oneHundredFortyEH_165517363774395139851590624004, phi_oneHundredFortyEH_165517363774395139851590624005,
    phi_oneHundredFortyEH_165517363774395139851590624006, phi_oneHundredFortyEH_165517363774395139851590624007, phi_oneHundredFortyEH_165517363774395139851590624008,
    phi_oneHundredFortyEH_165517363774395139851590624009, phi_oneHundredFortyEH_165517363774395139851590624010, phi_oneHundredFortyEH_165517363774395139851590624011,
    phi_oneHundredFortyEH_165517363774395139851590624012, phi_oneHundredFortyEH_165517363774395139851590624013, phi_oneHundredFortyEH_165517363774395139851590624014,
    phi_oneHundredFortyEH_165517363774395139851590624015, phi_oneHundredFortyEH_165517363774395139851590624016, phi_oneHundredFortyEH_165517363774395139851590624017,
    phi_oneHundredFortyEH_165517363774395139851590624018, phi_oneHundredFortyEH_165517363774395139851590624019, phi_oneHundredFortyEH_165517363774395139851590624020,
    phi_oneHundredFortyEH_165517363774395139851590624021, phi_oneHundredFortyEH_165517363774395139851590624022, phi_oneHundredFortyEH_165517363774395139851590624023,
    phi_oneHundredFortyEH_165517363774395139851590624024, phi_oneHundredFortyEH_165517363774395139851590624025, phi_oneHundredFortyEH_165517363774395139851590624026,
    phi_oneHundredFortyEH_165517363774395139851590624027, phi_oneHundredFortyEH_165517363774395139851590624028, phi_oneHundredFortyEH_165517363774395139851590624029,
    phi_oneHundredFortyEH_165517363774395139851590624030, phi_oneHundredFortyEH_165517363774395139851590624031, phi_oneHundredFortyEH_165517363774395139851590624032,
    phi_oneHundredFortyEH_165517363774395139851590624033, phi_oneHundredFortyEH_165517363774395139851590624034, phi_oneHundredFortyEH_165517363774395139851590624035,
    phi_oneHundredFortyEH_165517363774395139851590624036, phi_oneHundredFortyEH_165517363774395139851590624037, phi_oneHundredFortyEH_165517363774395139851590624038,
    phi_oneHundredFortyEH_165517363774395139851590624039, phi_oneHundredFortyEH_165517363774395139851590624040, phi_oneHundredFortyEH_165517363774395139851590624041,
    phi_oneHundredFortyEH_165517363774395139851590624042, phi_oneHundredFortyEH_165517363774395139851590624043, phi_oneHundredFortyEH_165517363774395139851590624044,
    phi_oneHundredFortyEH_165517363774395139851590624045, phi_oneHundredFortyEH_165517363774395139851590624046, phi_oneHundredFortyEH_165517363774395139851590624047,
    phi_oneHundredFortyEH_165517363774395139851590624048, phi_oneHundredFortyEH_165517363774395139851590624049, phi_oneHundredFortyEH_165517363774395139851590624050,
    phi_oneHundredFortyEH_165517363774395139851590624051, phi_oneHundredFortyEH_165517363774395139851590624052, phi_oneHundredFortyEH_165517363774395139851590624053,
    phi_oneHundredFortyEH_165517363774395139851590624054, phi_oneHundredFortyEH_165517363774395139851590624055, phi_oneHundredFortyEH_165517363774395139851590624056,
    phi_oneHundredFortyEH_165517363774395139851590624057, phi_oneHundredFortyEH_165517363774395139851590624058, phi_oneHundredFortyEH_165517363774395139851590624059,
    phi_oneHundredFortyEH_165517363774395139851590624060, phi_oneHundredFortyEH_165517363774395139851590624061, phi_oneHundredFortyEH_165517363774395139851590624062,
    phi_oneHundredFortyEH_165517363774395139851590624063, phi_oneHundredFortyEH_165517363774395139851590624064, phi_oneHundredFortyEH_165517363774395139851590624065,
    phi_oneHundredFortyEH_165517363774395139851590624066, phi_oneHundredFortyEH_165517363774395139851590624067, phi_oneHundredFortyEH_165517363774395139851590624068,
    phi_oneHundredFortyEH_165517363774395139851590624069, phi_oneHundredFortyEH_165517363774395139851590624070, phi_oneHundredFortyEH_165517363774395139851590624071,
    phi_oneHundredFortyEH_165517363774395139851590624072, phi_oneHundredFortyEH_165517363774395139851590624073, phi_oneHundredFortyEH_165517363774395139851590624074,
    phi_oneHundredFortyEH_165517363774395139851590624075, phi_oneHundredFortyEH_165517363774395139851590624076, phi_oneHundredFortyEH_165517363774395139851590624077,
    phi_oneHundredFortyEH_165517363774395139851590624078, phi_oneHundredFortyEH_165517363774395139851590624079, phi_oneHundredFortyEH_165517363774395139851590624080,
    phi_oneHundredFortyEH_165517363774395139851590624081, phi_oneHundredFortyEH_165517363774395139851590624082, phi_oneHundredFortyEH_165517363774395139851590624083,
    phi_oneHundredFortyEH_165517363774395139851590624084, phi_oneHundredFortyEH_165517363774395139851590624085, phi_oneHundredFortyEH_165517363774395139851590624086,
    phi_oneHundredFortyEH_165517363774395139851590624087, phi_oneHundredFortyEH_165517363774395139851590624088, phi_oneHundredFortyEH_165517363774395139851590624089,
    phi_oneHundredFortyEH_165517363774395139851590624090, phi_oneHundredFortyEH_165517363774395139851590624091, phi_oneHundredFortyEH_165517363774395139851590624092,
    phi_oneHundredFortyEH_165517363774395139851590624093, phi_oneHundredFortyEH_165517363774395139851590624094, phi_oneHundredFortyEH_165517363774395139851590624095,
    phi_oneHundredFortyEH_165517363774395139851590624096, phi_oneHundredFortyEH_165517363774395139851590624097, phi_oneHundredFortyEH_165517363774395139851590624098,
    phi_oneHundredFortyEH_165517363774395139851590624099, phi_oneHundredFortyEH_165517363774395139851590624100, phi_oneHundredFortyEH_165517363774395139851590624101]

end TotientTailPeriodKiller
end Erdos249257
