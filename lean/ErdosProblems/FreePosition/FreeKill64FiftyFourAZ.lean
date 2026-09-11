import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftyFourAZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftyFourAZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftyFourAZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftyFourAZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftyFourAZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftyFourAZFastPow a n * fiftyFourAZFastPow a n * a
        else fiftyFourAZFastPow a n * fiftyFourAZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftyFourAZ_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftyFourAZ_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftyFourAZ_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftyFourAZ_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftyFourAZ_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftyFourAZ_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftyFourAZ_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftyFourAZ_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftyFourAZ_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftyFourAZ_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftyFourAZ_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftyFourAZ_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftyFourAZ_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftyFourAZ_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftyFourAZ_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftyFourAZ_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftyFourAZ_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftyFourAZ_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftyFourAZ_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftyFourAZ_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftyFourAZ_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftyFourAZ_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftyFourAZ_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftyFourAZ_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftyFourAZ_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftyFourAZ_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftyFourAZ_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftyFourAZ_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftyFourAZ_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftyFourAZ_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftyFourAZ_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftyFourAZ_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftyFourAZ_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftyFourAZ_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftyFourAZ_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftyFourAZ_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftyFourAZ_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftyFourAZ_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftyFourAZ_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftyFourAZ_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftyFourAZ_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftyFourAZ_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftyFourAZ_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftyFourAZ_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftyFourAZ_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftyFourAZ_199 : Nat.Prime 199 := by norm_num
private theorem prime_fiftyFourAZ_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftyFourAZ_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftyFourAZ_227 : Nat.Prime 227 := by norm_num
private theorem prime_fiftyFourAZ_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftyFourAZ_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftyFourAZ_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftyFourAZ_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftyFourAZ_263 : Nat.Prime 263 := by norm_num
private theorem prime_fiftyFourAZ_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftyFourAZ_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftyFourAZ_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftyFourAZ_281 : Nat.Prime 281 := by norm_num
private theorem prime_fiftyFourAZ_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftyFourAZ_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftyFourAZ_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftyFourAZ_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftyFourAZ_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftyFourAZ_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftyFourAZ_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftyFourAZ_359 : Nat.Prime 359 := by norm_num
private theorem prime_fiftyFourAZ_367 : Nat.Prime 367 := by norm_num
private theorem prime_fiftyFourAZ_383 : Nat.Prime 383 := by norm_num
private theorem prime_fiftyFourAZ_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftyFourAZ_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftyFourAZ_421 : Nat.Prime 421 := by norm_num
private theorem prime_fiftyFourAZ_439 : Nat.Prime 439 := by norm_num
private theorem prime_fiftyFourAZ_443 : Nat.Prime 443 := by norm_num
private theorem prime_fiftyFourAZ_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftyFourAZ_457 : Nat.Prime 457 := by norm_num
private theorem prime_fiftyFourAZ_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftyFourAZ_479 : Nat.Prime 479 := by norm_num
private theorem prime_fiftyFourAZ_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftyFourAZ_547 : Nat.Prime 547 := by norm_num
private theorem prime_fiftyFourAZ_557 : Nat.Prime 557 := by norm_num
private theorem prime_fiftyFourAZ_563 : Nat.Prime 563 := by norm_num
private theorem prime_fiftyFourAZ_569 : Nat.Prime 569 := by norm_num
private theorem prime_fiftyFourAZ_577 : Nat.Prime 577 := by norm_num
private theorem prime_fiftyFourAZ_587 : Nat.Prime 587 := by norm_num
private theorem prime_fiftyFourAZ_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftyFourAZ_641 : Nat.Prime 641 := by norm_num
private theorem prime_fiftyFourAZ_659 : Nat.Prime 659 := by norm_num
private theorem prime_fiftyFourAZ_683 : Nat.Prime 683 := by norm_num
private theorem prime_fiftyFourAZ_691 : Nat.Prime 691 := by norm_num
private theorem prime_fiftyFourAZ_701 : Nat.Prime 701 := by norm_num
private theorem prime_fiftyFourAZ_739 : Nat.Prime 739 := by norm_num
private theorem prime_fiftyFourAZ_751 : Nat.Prime 751 := by norm_num
private theorem prime_fiftyFourAZ_761 : Nat.Prime 761 := by norm_num
private theorem prime_fiftyFourAZ_769 : Nat.Prime 769 := by norm_num
private theorem prime_fiftyFourAZ_787 : Nat.Prime 787 := by norm_num
private theorem prime_fiftyFourAZ_811 : Nat.Prime 811 := by norm_num
private theorem prime_fiftyFourAZ_821 : Nat.Prime 821 := by norm_num
private theorem prime_fiftyFourAZ_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftyFourAZ_863 : Nat.Prime 863 := by norm_num
private theorem prime_fiftyFourAZ_877 : Nat.Prime 877 := by norm_num
private theorem prime_fiftyFourAZ_881 : Nat.Prime 881 := by norm_num
private theorem prime_fiftyFourAZ_907 : Nat.Prime 907 := by norm_num
private theorem prime_fiftyFourAZ_919 : Nat.Prime 919 := by norm_num
private theorem prime_fiftyFourAZ_947 : Nat.Prime 947 := by norm_num
private theorem prime_fiftyFourAZ_953 : Nat.Prime 953 := by norm_num
private theorem prime_fiftyFourAZ_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftyFourAZ_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fiftyFourAZ_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fiftyFourAZ_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_fiftyFourAZ_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fiftyFourAZ_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fiftyFourAZ_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_fiftyFourAZ_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftyFourAZ_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_fiftyFourAZ_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_fiftyFourAZ_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fiftyFourAZ_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_fiftyFourAZ_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fiftyFourAZ_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_fiftyFourAZ_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fiftyFourAZ_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fiftyFourAZ_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fiftyFourAZ_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fiftyFourAZ_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_fiftyFourAZ_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_fiftyFourAZ_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fiftyFourAZ_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_fiftyFourAZ_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_fiftyFourAZ_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_fiftyFourAZ_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_fiftyFourAZ_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_fiftyFourAZ_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_fiftyFourAZ_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_fiftyFourAZ_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_fiftyFourAZ_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_fiftyFourAZ_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_fiftyFourAZ_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_fiftyFourAZ_1823 : Nat.Prime 1823 := by norm_num
private theorem prime_fiftyFourAZ_1889 : Nat.Prime 1889 := by norm_num
private theorem prime_fiftyFourAZ_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_fiftyFourAZ_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_fiftyFourAZ_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fiftyFourAZ_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_fiftyFourAZ_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_fiftyFourAZ_2131 : Nat.Prime 2131 := by norm_num
private theorem prime_fiftyFourAZ_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fiftyFourAZ_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_fiftyFourAZ_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_fiftyFourAZ_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_fiftyFourAZ_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_fiftyFourAZ_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_fiftyFourAZ_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_fiftyFourAZ_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_fiftyFourAZ_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_fiftyFourAZ_2663 : Nat.Prime 2663 := by norm_num
private theorem prime_fiftyFourAZ_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_fiftyFourAZ_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_fiftyFourAZ_2749 : Nat.Prime 2749 := by norm_num
private theorem prime_fiftyFourAZ_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_fiftyFourAZ_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_fiftyFourAZ_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_fiftyFourAZ_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_fiftyFourAZ_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_fiftyFourAZ_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_fiftyFourAZ_3163 : Nat.Prime 3163 := by norm_num
private theorem prime_fiftyFourAZ_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_fiftyFourAZ_3257 : Nat.Prime 3257 := by norm_num
private theorem prime_fiftyFourAZ_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_fiftyFourAZ_3359 : Nat.Prime 3359 := by norm_num
private theorem prime_fiftyFourAZ_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_fiftyFourAZ_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_fiftyFourAZ_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_fiftyFourAZ_3947 : Nat.Prime 3947 := by norm_num
private theorem prime_fiftyFourAZ_4091 : Nat.Prime 4091 := by norm_num
private theorem prime_fiftyFourAZ_4157 : Nat.Prime 4157 := by norm_num
private theorem prime_fiftyFourAZ_4177 : Nat.Prime 4177 := by norm_num
private theorem prime_fiftyFourAZ_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_fiftyFourAZ_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_fiftyFourAZ_4273 : Nat.Prime 4273 := by norm_num
private theorem prime_fiftyFourAZ_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_fiftyFourAZ_4877 : Nat.Prime 4877 := by norm_num
private theorem prime_fiftyFourAZ_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_fiftyFourAZ_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_fiftyFourAZ_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftyFourAZ_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_fiftyFourAZ_5237 : Nat.Prime 5237 := by norm_num
private theorem prime_fiftyFourAZ_5297 : Nat.Prime 5297 := by norm_num
private theorem prime_fiftyFourAZ_5437 : Nat.Prime 5437 := by norm_num
private theorem prime_fiftyFourAZ_5443 : Nat.Prime 5443 := by norm_num
private theorem prime_fiftyFourAZ_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_fiftyFourAZ_5557 : Nat.Prime 5557 := by norm_num
private theorem prime_fiftyFourAZ_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_fiftyFourAZ_5659 : Nat.Prime 5659 := by norm_num
private theorem prime_fiftyFourAZ_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_fiftyFourAZ_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_fiftyFourAZ_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_fiftyFourAZ_6121 : Nat.Prime 6121 := by norm_num
private theorem prime_fiftyFourAZ_6131 : Nat.Prime 6131 := by norm_num
private theorem prime_fiftyFourAZ_6163 : Nat.Prime 6163 := by norm_num
private theorem prime_fiftyFourAZ_6257 : Nat.Prime 6257 := by norm_num
private theorem prime_fiftyFourAZ_6271 : Nat.Prime 6271 := by norm_num
private theorem prime_fiftyFourAZ_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fiftyFourAZ_6823 : Nat.Prime 6823 := by norm_num
private theorem prime_fiftyFourAZ_6983 : Nat.Prime 6983 := by norm_num
private theorem prime_fiftyFourAZ_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_fiftyFourAZ_7159 : Nat.Prime 7159 := by norm_num
private theorem prime_fiftyFourAZ_7229 : Nat.Prime 7229 := by norm_num
private theorem prime_fiftyFourAZ_7481 : Nat.Prime 7481 := by norm_num
private theorem prime_fiftyFourAZ_7499 : Nat.Prime 7499 := by norm_num
private theorem prime_fiftyFourAZ_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_fiftyFourAZ_7907 : Nat.Prime 7907 := by norm_num
private theorem prime_fiftyFourAZ_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_fiftyFourAZ_8123 : Nat.Prime 8123 := by norm_num
private theorem prime_fiftyFourAZ_8171 : Nat.Prime 8171 := by norm_num
private theorem prime_fiftyFourAZ_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fiftyFourAZ_8291 : Nat.Prime 8291 := by norm_num
private theorem prime_fiftyFourAZ_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fiftyFourAZ_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fiftyFourAZ_8699 : Nat.Prime 8699 := by norm_num
private theorem prime_fiftyFourAZ_8713 : Nat.Prime 8713 := by norm_num
private theorem prime_fiftyFourAZ_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_fiftyFourAZ_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_fiftyFourAZ_8837 : Nat.Prime 8837 := by norm_num
private theorem prime_fiftyFourAZ_9281 : Nat.Prime 9281 := by norm_num
private theorem prime_fiftyFourAZ_9587 : Nat.Prime 9587 := by norm_num
private theorem prime_fiftyFourAZ_9613 : Nat.Prime 9613 := by norm_num
private theorem prime_fiftyFourAZ_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_fiftyFourAZ_9743 : Nat.Prime 9743 := by norm_num
private theorem prime_fiftyFourAZ_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_fiftyFourAZ_9931 : Nat.Prime 9931 := by norm_num
private theorem prime_fiftyFourAZ_11257 : Nat.Prime 11257 := by norm_num
private theorem prime_fiftyFourAZ_11489 : Nat.Prime 11489 := by norm_num
private theorem prime_fiftyFourAZ_11821 : Nat.Prime 11821 := by norm_num
private theorem prime_fiftyFourAZ_12289 : Nat.Prime 12289 := by norm_num
private theorem prime_fiftyFourAZ_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_fiftyFourAZ_13217 : Nat.Prime 13217 := by norm_num
private theorem prime_fiftyFourAZ_13751 : Nat.Prime 13751 := by norm_num
private theorem prime_fiftyFourAZ_14143 : Nat.Prime 14143 := by norm_num
private theorem prime_fiftyFourAZ_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_fiftyFourAZ_14347 : Nat.Prime 14347 := by norm_num
private theorem prime_fiftyFourAZ_15427 : Nat.Prime 15427 := by norm_num
private theorem prime_fiftyFourAZ_16091 : Nat.Prime 16091 := by norm_num
private theorem prime_fiftyFourAZ_17047 : Nat.Prime 17047 := by norm_num
private theorem prime_fiftyFourAZ_17191 : Nat.Prime 17191 := by norm_num
private theorem prime_fiftyFourAZ_18679 : Nat.Prime 18679 := by norm_num
private theorem prime_fiftyFourAZ_19309 : Nat.Prime 19309 := by norm_num
private theorem prime_fiftyFourAZ_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_fiftyFourAZ_21929 : Nat.Prime 21929 := by norm_num
private theorem prime_fiftyFourAZ_23537 : Nat.Prime 23537 := by norm_num
private theorem prime_fiftyFourAZ_24421 : Nat.Prime 24421 := by norm_num
private theorem prime_fiftyFourAZ_25903 : Nat.Prime 25903 := by norm_num
private theorem prime_fiftyFourAZ_25913 : Nat.Prime 25913 := by norm_num
private theorem prime_fiftyFourAZ_26171 : Nat.Prime 26171 := by norm_num
private theorem prime_fiftyFourAZ_26417 : Nat.Prime 26417 := by norm_num
private theorem prime_fiftyFourAZ_27067 : Nat.Prime 27067 := by norm_num
private theorem prime_fiftyFourAZ_30911 : Nat.Prime 30911 := by norm_num
private theorem prime_fiftyFourAZ_32051 : Nat.Prime 32051 := by norm_num
private theorem prime_fiftyFourAZ_33749 : Nat.Prime 33749 := by norm_num
private theorem prime_fiftyFourAZ_34781 : Nat.Prime 34781 := by norm_num
private theorem prime_fiftyFourAZ_34981 : Nat.Prime 34981 := by norm_num
private theorem prime_fiftyFourAZ_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fiftyFourAZ_35911 : Nat.Prime 35911 := by norm_num
private theorem prime_fiftyFourAZ_36107 : Nat.Prime 36107 := by norm_num
private theorem prime_fiftyFourAZ_39157 : Nat.Prime 39157 := by norm_num
private theorem prime_fiftyFourAZ_43457 : Nat.Prime 43457 := by norm_num
private theorem prime_fiftyFourAZ_43499 : Nat.Prime 43499 := by norm_num
private theorem prime_fiftyFourAZ_43541 : Nat.Prime 43541 := by norm_num
private theorem prime_fiftyFourAZ_50543 : Nat.Prime 50543 := by norm_num
private theorem prime_fiftyFourAZ_50591 : Nat.Prime 50591 := by norm_num
private theorem prime_fiftyFourAZ_53849 : Nat.Prime 53849 := by norm_num
private theorem prime_fiftyFourAZ_55291 : Nat.Prime 55291 := by norm_num
private theorem prime_fiftyFourAZ_56269 : Nat.Prime 56269 := by norm_num
private theorem prime_fiftyFourAZ_60793 : Nat.Prime 60793 := by norm_num
private theorem prime_fiftyFourAZ_61487 : Nat.Prime 61487 := by norm_num
private theorem prime_fiftyFourAZ_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fiftyFourAZ_63487 : Nat.Prime 63487 := by norm_num
private theorem prime_fiftyFourAZ_67079 : Nat.Prime 67079 := by norm_num
private theorem prime_fiftyFourAZ_67819 : Nat.Prime 67819 := by norm_num
private theorem prime_fiftyFourAZ_68713 : Nat.Prime 68713 := by norm_num
private theorem prime_fiftyFourAZ_73571 : Nat.Prime 73571 := by norm_num
private theorem prime_fiftyFourAZ_76543 : Nat.Prime 76543 := by norm_num
private theorem prime_fiftyFourAZ_76679 : Nat.Prime 76679 := by norm_num
private theorem prime_fiftyFourAZ_79063 : Nat.Prime 79063 := by norm_num
private theorem prime_fiftyFourAZ_80149 : Nat.Prime 80149 := by norm_num
private theorem prime_fiftyFourAZ_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fiftyFourAZ_91009 : Nat.Prime 91009 := by norm_num
private theorem prime_fiftyFourAZ_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fiftyFourAZ_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_fiftyFourAZ_109481 : Nat.Prime 109481 := by norm_num
private theorem prime_fiftyFourAZ_110261 : Nat.Prime 110261 := by norm_num
private theorem prime_fiftyFourAZ_113819 : Nat.Prime 113819 := by norm_num
private theorem prime_fiftyFourAZ_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fiftyFourAZ_115001 : Nat.Prime 115001 := by norm_num
private theorem prime_fiftyFourAZ_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_fiftyFourAZ_124853 : Nat.Prime 124853 := by norm_num
private theorem prime_fiftyFourAZ_127997 : Nat.Prime 127997 := by norm_num
private theorem prime_fiftyFourAZ_130787 : Nat.Prime 130787 := by norm_num
private theorem prime_fiftyFourAZ_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_fiftyFourAZ_143881 : Nat.Prime 143881 := by norm_num
private theorem prime_fiftyFourAZ_150791 : Nat.Prime 150791 := by norm_num
private theorem prime_fiftyFourAZ_152809 : Nat.Prime 152809 := by norm_num
private theorem prime_fiftyFourAZ_154621 : Nat.Prime 154621 := by norm_num
private theorem prime_fiftyFourAZ_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fiftyFourAZ_167071 : Nat.Prime 167071 := by norm_num
private theorem prime_fiftyFourAZ_183451 : Nat.Prime 183451 := by norm_num
private theorem prime_fiftyFourAZ_186481 : Nat.Prime 186481 := by norm_num
private theorem prime_fiftyFourAZ_189067 : Nat.Prime 189067 := by norm_num
private theorem prime_fiftyFourAZ_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_fiftyFourAZ_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fiftyFourAZ_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fiftyFourAZ_227893 : Nat.Prime 227893 := by norm_num
private theorem prime_fiftyFourAZ_246391 : Nat.Prime 246391 := by norm_num
private theorem prime_fiftyFourAZ_253853 : Nat.Prime 253853 := by norm_num
private theorem prime_fiftyFourAZ_263899 : Nat.Prime 263899 := by norm_num
private theorem prime_fiftyFourAZ_277259 : Nat.Prime 277259 := by norm_num
private theorem prime_fiftyFourAZ_292231 : Nat.Prime 292231 := by norm_num
private theorem prime_fiftyFourAZ_301649 : Nat.Prime 301649 := by norm_num
private theorem prime_fiftyFourAZ_303377 : Nat.Prime 303377 := by norm_num
private theorem prime_fiftyFourAZ_312979 : Nat.Prime 312979 := by norm_num
private theorem prime_fiftyFourAZ_327337 : Nat.Prime 327337 := by norm_num
private theorem prime_fiftyFourAZ_328103 : Nat.Prime 328103 := by norm_num
private theorem prime_fiftyFourAZ_341087 : Nat.Prime 341087 := by norm_num
private theorem prime_fiftyFourAZ_342553 : Nat.Prime 342553 := by norm_num
private theorem prime_fiftyFourAZ_344429 : Nat.Prime 344429 := by norm_num
private theorem prime_fiftyFourAZ_361727 : Nat.Prime 361727 := by norm_num
private theorem prime_fiftyFourAZ_365699 : Nat.Prime 365699 := by norm_num
private theorem prime_fiftyFourAZ_372401 : Nat.Prime 372401 := by norm_num
private theorem prime_fiftyFourAZ_385607 : Nat.Prime 385607 := by norm_num
private theorem prime_fiftyFourAZ_394819 : Nat.Prime 394819 := by norm_num
private theorem prime_fiftyFourAZ_403079 : Nat.Prime 403079 := by norm_num
private theorem prime_fiftyFourAZ_425291 : Nat.Prime 425291 := by norm_num
private theorem prime_fiftyFourAZ_455881 : Nat.Prime 455881 := by norm_num
private theorem prime_fiftyFourAZ_461233 : Nat.Prime 461233 := by norm_num
private theorem prime_fiftyFourAZ_471217 : Nat.Prime 471217 := by norm_num
private theorem prime_fiftyFourAZ_472883 : Nat.Prime 472883 := by norm_num
private theorem prime_fiftyFourAZ_475637 : Nat.Prime 475637 := by norm_num
private theorem prime_fiftyFourAZ_478727 : Nat.Prime 478727 := by norm_num
private theorem prime_fiftyFourAZ_481513 : Nat.Prime 481513 := by norm_num
private theorem prime_fiftyFourAZ_568163 : Nat.Prime 568163 := by norm_num
private theorem prime_fiftyFourAZ_572879 : Nat.Prime 572879 := by norm_num
private theorem prime_fiftyFourAZ_634031 : Nat.Prime 634031 := by norm_num
private theorem prime_fiftyFourAZ_644701 : Nat.Prime 644701 := by norm_num
private theorem prime_fiftyFourAZ_666467 : Nat.Prime 666467 := by norm_num
private theorem prime_fiftyFourAZ_687647 : Nat.Prime 687647 := by norm_num
private theorem prime_fiftyFourAZ_712477 : Nat.Prime 712477 := by norm_num
private theorem prime_fiftyFourAZ_758827 : Nat.Prime 758827 := by norm_num
private theorem prime_fiftyFourAZ_864917 : Nat.Prime 864917 := by norm_num
private theorem prime_fiftyFourAZ_901177 : Nat.Prime 901177 := by norm_num
private theorem prime_fiftyFourAZ_963499 : Nat.Prime 963499 := by norm_num
private theorem prime_fiftyFourAZ_971149 : Nat.Prime 971149 := by norm_num
private theorem prime_fiftyFourAZ_977323 : Nat.Prime 977323 := by norm_num
private theorem prime_fiftyFourAZ_1032763 : Nat.Prime 1032763 := by norm_num
private theorem prime_fiftyFourAZ_1126577 : Nat.Prime 1126577 := by norm_num
private theorem prime_fiftyFourAZ_1141573 : Nat.Prime 1141573 := by norm_num
private theorem prime_fiftyFourAZ_1146931 : Nat.Prime 1146931 := by norm_num
private theorem prime_fiftyFourAZ_1173541 : Nat.Prime 1173541 := by norm_num
private theorem prime_fiftyFourAZ_1255693 : Nat.Prime 1255693 := by norm_num
private theorem prime_fiftyFourAZ_1323919 : Nat.Prime 1323919 := by norm_num
private theorem prime_fiftyFourAZ_1496657 : Nat.Prime 1496657 := by norm_num
private theorem prime_fiftyFourAZ_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fiftyFourAZ_1548389 : Nat.Prime 1548389 := by norm_num
private theorem prime_fiftyFourAZ_1686677 : Nat.Prime 1686677 := by norm_num
private theorem prime_fiftyFourAZ_1736237 : Nat.Prime 1736237 := by norm_num
private theorem prime_fiftyFourAZ_1922603 : Nat.Prime 1922603 := by norm_num
private theorem prime_fiftyFourAZ_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_fiftyFourAZ_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fiftyFourAZ_2202311 : Nat.Prime 2202311 := by norm_num
private theorem prime_fiftyFourAZ_2288681 : Nat.Prime 2288681 := by norm_num
private theorem prime_fiftyFourAZ_2303321 : Nat.Prime 2303321 := by norm_num
private theorem prime_fiftyFourAZ_2314271 : Nat.Prime 2314271 := by norm_num
private theorem prime_fiftyFourAZ_2431189 : Nat.Prime 2431189 := by norm_num
private theorem prime_fiftyFourAZ_2503121 : Nat.Prime 2503121 := by norm_num
private theorem prime_fiftyFourAZ_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fiftyFourAZ_2674733 : Nat.Prime 2674733 := by norm_num
private theorem prime_fiftyFourAZ_3593063 : Nat.Prime 3593063 := by norm_num
private theorem prime_fiftyFourAZ_3616901 : Nat.Prime 3616901 := by norm_num
private theorem prime_fiftyFourAZ_3656251 : Nat.Prime 3656251 := by norm_num
private theorem prime_fiftyFourAZ_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_fiftyFourAZ_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_fiftyFourAZ_4175827 : Nat.Prime 4175827 := by norm_num
private theorem prime_fiftyFourAZ_4805179 : Nat.Prime 4805179 := by norm_num
private theorem prime_fiftyFourAZ_4865743 : Nat.Prime 4865743 := by norm_num
private theorem prime_fiftyFourAZ_5004841 : Nat.Prime 5004841 := by norm_num
private theorem prime_fiftyFourAZ_5024269 : Nat.Prime 5024269 := by norm_num
private theorem prime_fiftyFourAZ_5026873 : Nat.Prime 5026873 := by norm_num
private theorem prime_fiftyFourAZ_5188849 : Nat.Prime 5188849 := by norm_num
private theorem prime_fiftyFourAZ_5205667 : Nat.Prime 5205667 := by norm_num
private theorem prime_fiftyFourAZ_5760217 : Nat.Prime 5760217 := by norm_num
private theorem prime_fiftyFourAZ_6528503 : Nat.Prime 6528503 := by norm_num
private theorem prime_fiftyFourAZ_6643829 : Nat.Prime 6643829 := by norm_num
private theorem prime_fiftyFourAZ_6646357 : Nat.Prime 6646357 := by norm_num
private theorem prime_fiftyFourAZ_6894983 : Nat.Prime 6894983 := by norm_num
private theorem prime_fiftyFourAZ_6914711 : Nat.Prime 6914711 := by norm_num
private theorem prime_fiftyFourAZ_7034639 : Nat.Prime 7034639 := by norm_num
private theorem prime_fiftyFourAZ_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fiftyFourAZ_7239721 : Nat.Prime 7239721 := by norm_num
private theorem prime_fiftyFourAZ_7524701 : Nat.Prime 7524701 := by norm_num
private theorem prime_fiftyFourAZ_7603997 : Nat.Prime 7603997 := by norm_num
private theorem prime_fiftyFourAZ_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fiftyFourAZ_8504393 : Nat.Prime 8504393 := by norm_num
private theorem prime_fiftyFourAZ_9063547 : Nat.Prime 9063547 := by norm_num
private theorem prime_fiftyFourAZ_9319789 : Nat.Prime 9319789 := by norm_num
private theorem prime_fiftyFourAZ_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fiftyFourAZ_10897001 : Nat.Prime 10897001 := by norm_num
private theorem prime_fiftyFourAZ_11208829 : Nat.Prime 11208829 := by norm_num
private theorem prime_fiftyFourAZ_11372171 : Nat.Prime 11372171 := by norm_num
private theorem prime_fiftyFourAZ_11968729 : Nat.Prime 11968729 := by norm_num
private theorem prime_fiftyFourAZ_12262583 : Nat.Prime 12262583 := by norm_num
private theorem prime_fiftyFourAZ_12910379 : Nat.Prime 12910379 := by norm_num
private theorem prime_fiftyFourAZ_12986273 : Nat.Prime 12986273 := by norm_num
private theorem prime_fiftyFourAZ_13265149 : Nat.Prime 13265149 := by norm_num
private theorem prime_fiftyFourAZ_13313779 : Nat.Prime 13313779 := by norm_num
private theorem prime_fiftyFourAZ_13926949 : Nat.Prime 13926949 := by norm_num
private theorem prime_fiftyFourAZ_14477077 : Nat.Prime 14477077 := by norm_num
private theorem prime_fiftyFourAZ_14626967 : Nat.Prime 14626967 := by norm_num
private theorem prime_fiftyFourAZ_14702459 : Nat.Prime 14702459 := by norm_num
private theorem prime_fiftyFourAZ_14821679 : Nat.Prime 14821679 := by norm_num
private theorem prime_fiftyFourAZ_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fiftyFourAZ_15058601 : Nat.Prime 15058601 := by norm_num
private theorem prime_fiftyFourAZ_16996403 : Nat.Prime 16996403 := by norm_num
private theorem prime_fiftyFourAZ_18046411 : Nat.Prime 18046411 := by norm_num
private theorem prime_fiftyFourAZ_19694039 : Nat.Prime 19694039 := by norm_num
private theorem prime_fiftyFourAZ_20025517 : Nat.Prime 20025517 := by norm_num
private theorem prime_fiftyFourAZ_20294777 : Nat.Prime 20294777 := by norm_num
private theorem prime_fiftyFourAZ_20353121 : Nat.Prime 20353121 := by norm_num
private theorem prime_fiftyFourAZ_21066299 : Nat.Prime 21066299 := by norm_num
private theorem prime_fiftyFourAZ_21417871 : Nat.Prime 21417871 := by norm_num
private theorem prime_fiftyFourAZ_23415331 : Nat.Prime 23415331 := by norm_num
private theorem prime_fiftyFourAZ_23462297 : Nat.Prime 23462297 := by norm_num
private theorem prime_fiftyFourAZ_24289169 : Nat.Prime 24289169 := by norm_num
private theorem prime_fiftyFourAZ_24442633 : Nat.Prime 24442633 := by norm_num
private theorem prime_fiftyFourAZ_24949783 : Nat.Prime 24949783 := by norm_num
private theorem prime_fiftyFourAZ_26126021 : Nat.Prime 26126021 := by norm_num
private theorem prime_fiftyFourAZ_26706613 : Nat.Prime 26706613 := by norm_num
private theorem prime_fiftyFourAZ_28245583 : Nat.Prime 28245583 := by norm_num
private theorem prime_fiftyFourAZ_29595263 : Nat.Prime 29595263 := by norm_num

private theorem prime_fiftyFourAZ_30919891 : Nat.Prime 30919891 := by
  apply lucas_primality 30919891 (3 : ZMod 30919891)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) = 30919891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_21929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30919891) ^ 15459945 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30919891) ^ 10306630 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30919891) ^ 6183978 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30919891) ^ 657870 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 30919891) ^ 1410 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_33992807 : Nat.Prime 33992807 := by
  apply lucas_primality 33992807 (5 : ZMod 33992807)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16996403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16996403, 1)] : List FactorBlock).map factorBlockValue).prod) = 33992807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_16996403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 33992807) ^ 16996403 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 33992807) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_37279157 : Nat.Prime 37279157 := by
  apply lucas_primality 37279157 (2 : ZMod 37279157)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9319789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9319789, 1)] : List FactorBlock).map factorBlockValue).prod) = 37279157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_9319789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37279157) ^ 18639578 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 37279157) ^ 4 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_39388079 : Nat.Prime 39388079 := by
  apply lucas_primality 39388079 (11 : ZMod 39388079)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19694039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19694039, 1)] : List FactorBlock).map factorBlockValue).prod) = 39388079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_19694039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 39388079) ^ 19694039 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 39388079) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_42559471 : Nat.Prime 42559471 := by
  apply lucas_primality 42559471 (6 : ZMod 42559471)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (472883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (472883, 1)] : List FactorBlock).map factorBlockValue).prod) = 42559471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_472883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42559471) ^ 21279735 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 14186490 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 8511894 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 42559471) ^ 90 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_43060817 : Nat.Prime 43060817 := by
  apply lucas_primality 43060817 (3 : ZMod 43060817)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (271, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (271, 1), (9931, 1)] : List FactorBlock).map factorBlockValue).prod) = 43060817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_271
      · exact prime_fiftyFourAZ_9931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43060817) ^ 21530408 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 43060817) ^ 158896 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 43060817) ^ 4336 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_47667947 : Nat.Prime 47667947 := by
  apply lucas_primality 47667947 (2 : ZMod 47667947)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4289, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4289, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod) = 47667947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_4289
      · exact prime_fiftyFourAZ_5557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47667947) ^ 23833973 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47667947) ^ 11114 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47667947) ^ 8578 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_55052689 : Nat.Prime 55052689 := by
  apply lucas_primality 55052689 (7 : ZMod 55052689)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1146931, 1)] : List FactorBlock).map factorBlockValue).prod) = 55052689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1146931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 55052689) ^ 27526344 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 18350896 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 55052689) ^ 48 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_64574753 : Nat.Prime 64574753 := by
  apply lucas_primality 64574753 (3 : ZMod 64574753)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (183451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (183451, 1)] : List FactorBlock).map factorBlockValue).prod) = 64574753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_183451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64574753) ^ 32287376 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64574753) ^ 5870432 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64574753) ^ 352 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_66463571 : Nat.Prime 66463571 := by
  apply lucas_primality 66463571 (2 : ZMod 66463571)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6646357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6646357, 1)] : List FactorBlock).map factorBlockValue).prod) = 66463571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_6646357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 66463571) ^ 33231785 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 66463571) ^ 13292714 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 66463571) ^ 10 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_69198781 : Nat.Prime 69198781 := by
  apply lucas_primality 69198781 (13 : ZMod 69198781)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (23537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (23537, 1)] : List FactorBlock).map factorBlockValue).prod) = 69198781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_23537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 69198781) ^ 34599390 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 23066260 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 13839756 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 9885540 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 69198781) ^ 2940 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_69813937 : Nat.Prime 69813937 := by
  apply lucas_primality 69813937 (10 : ZMod 69813937)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (271, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (271, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 69813937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_271
      · exact prime_fiftyFourAZ_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 69813937) ^ 34906968 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 23271312 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 257616 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 69813937) ^ 39024 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_77218987 : Nat.Prime 77218987 := by
  apply lucas_primality 77218987 (5 : ZMod 77218987)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (18679, 1)] : List FactorBlock).map factorBlockValue).prod) = 77218987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_18679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77218987) ^ 38609493 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 25739662 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 5939922 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 1456962 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77218987) ^ 4134 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_77917639 : Nat.Prime 77917639 := by
  apply lucas_primality 77917639 (6 : ZMod 77917639)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12986273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12986273, 1)] : List FactorBlock).map factorBlockValue).prod) = 77917639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_12986273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 77917639) ^ 38958819 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77917639) ^ 25972546 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77917639) ^ 6 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_79594331 : Nat.Prime 79594331 := by
  apply lucas_primality 79594331 (2 : ZMod 79594331)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (463, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (463, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) = 79594331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_463
      · exact prime_fiftyFourAZ_17191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79594331) ^ 39797165 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 15918866 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 171910 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 79594331) ^ 4630 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_121733501 : Nat.Prime 121733501 := by
  apply lucas_primality 121733501 (3 : ZMod 121733501)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) = 121733501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_34781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121733501) ^ 60866750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 24346700 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 17390500 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 121733501) ^ 3500 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_126749873 : Nat.Prime 126749873 := by
  apply lucas_primality 126749873 (3 : ZMod 126749873)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (344429, 1)] : List FactorBlock).map factorBlockValue).prod) = 126749873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_344429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 126749873) ^ 63374936 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 5510864 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 126749873) ^ 368 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_142723051 : Nat.Prime 142723051 := by
  apply lucas_primality 142723051 (10 : ZMod 142723051)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (23, 1), (41, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (23, 1), (41, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 142723051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 142723051) ^ 71361525 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 47574350 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 28544610 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 6205350 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 3481050 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 142723051) ^ 141450 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_145843909 : Nat.Prime 145843909 := by
  apply lucas_primality 145843909 (2 : ZMod 145843909)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1736237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1736237, 1)] : List FactorBlock).map factorBlockValue).prod) = 145843909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_1736237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145843909) ^ 72921954 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 145843909) ^ 48614636 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 145843909) ^ 20834844 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 145843909) ^ 84 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_151632149 : Nat.Prime 151632149 := by
  apply lucas_primality 151632149 (2 : ZMod 151632149)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (137, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 151632149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_89
      · exact prime_fiftyFourAZ_137
      · exact prime_fiftyFourAZ_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151632149) ^ 75816074 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 1703732 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 1106804 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 151632149) ^ 48772 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_154032929 : Nat.Prime 154032929 := by
  apply lucas_primality 154032929 (3 : ZMod 154032929)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (687647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (687647, 1)] : List FactorBlock).map factorBlockValue).prod) = 154032929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_687647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 154032929) ^ 77016464 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 154032929) ^ 22004704 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 154032929) ^ 224 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_167123389 : Nat.Prime 167123389 := by
  apply lucas_primality 167123389 (2 : ZMod 167123389)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13926949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13926949, 1)] : List FactorBlock).map factorBlockValue).prod) = 167123389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13926949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167123389) ^ 83561694 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 167123389) ^ 55707796 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 167123389) ^ 12 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_131
      · exact prime_fiftyFourAZ_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_180464111 : Nat.Prime 180464111 := by
  apply lucas_primality 180464111 (7 : ZMod 180464111)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18046411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18046411, 1)] : List FactorBlock).map factorBlockValue).prod) = 180464111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_18046411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 180464111) ^ 90232055 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 180464111) ^ 36092822 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 180464111) ^ 10 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_188916269 : Nat.Prime 188916269 := by
  apply lucas_primality 188916269 (2 : ZMod 188916269)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (271, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (271, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod) = 188916269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_61
      · exact prime_fiftyFourAZ_271
      · exact prime_fiftyFourAZ_2857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 188916269) ^ 94458134 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 3096988 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 697108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188916269) ^ 66124 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_209281249 : Nat.Prime 209281249 := by
  apply lucas_primality 209281249 (13 : ZMod 209281249)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (31, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (31, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 209281249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 209281249) ^ 104640624 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 69760416 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 19025568 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 6751008 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 209281249) ^ 98208 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_219934111 : Nat.Prime 219934111 := by
  apply lucas_primality 219934111 (3 : ZMod 219934111)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (666467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (666467, 1)] : List FactorBlock).map factorBlockValue).prod) = 219934111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_666467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 219934111) ^ 109967055 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 219934111) ^ 73311370 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 219934111) ^ 43986822 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 219934111) ^ 19994010 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 219934111) ^ 330 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_191
      · exact prime_fiftyFourAZ_383
      · exact prime_fiftyFourAZ_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_239061077 : Nat.Prime 239061077 := by
  apply lucas_primality 239061077 (2 : ZMod 239061077)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (303377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (303377, 1)] : List FactorBlock).map factorBlockValue).prod) = 239061077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_197
      · exact prime_fiftyFourAZ_303377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 239061077) ^ 119530538 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 239061077) ^ 1213508 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 239061077) ^ 788 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_246594239 : Nat.Prime 246594239 := by
  apply lucas_primality 246594239 (11 : ZMod 246594239)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (11208829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (11208829, 1)] : List FactorBlock).map factorBlockValue).prod) = 246594239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_11208829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 246594239) ^ 123297119 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 246594239) ^ 22417658 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 246594239) ^ 22 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_269802739 : Nat.Prime 269802739 := by
  apply lucas_primality 269802739 (13 : ZMod 269802739)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1213, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1213, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) = 269802739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1213
      · exact prime_fiftyFourAZ_1373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 269802739) ^ 134901369 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 269802739) ^ 89934246 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 269802739) ^ 222426 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 269802739) ^ 196506 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_281055143 : Nat.Prime 281055143 := by
  apply lucas_primality 281055143 (5 : ZMod 281055143)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (312979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (312979, 1)] : List FactorBlock).map factorBlockValue).prod) = 281055143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_449
      · exact prime_fiftyFourAZ_312979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 281055143) ^ 140527571 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 281055143) ^ 625958 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 281055143) ^ 898 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_287249497 : Nat.Prime 287249497 := by
  apply lucas_primality 287249497 (5 : ZMod 287249497)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11968729, 1)] : List FactorBlock).map factorBlockValue).prod) = 287249497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11968729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287249497) ^ 143624748 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 95749832 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 287249497) ^ 24 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_302460083 : Nat.Prime 302460083 := by
  apply lucas_primality 302460083 (2 : ZMod 302460083)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (53, 1), (61, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (53, 1), (61, 1), (1613, 1)] : List FactorBlock).map factorBlockValue).prod) = 302460083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_61
      · exact prime_fiftyFourAZ_1613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 302460083) ^ 151230041 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 10429658 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 5706794 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 4958362 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302460083) ^ 187514 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_312018557 : Nat.Prime 312018557 := by
  apply lucas_primality 312018557 (2 : ZMod 312018557)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5437, 1), (14347, 1)] : List FactorBlock).map factorBlockValue).prod) = 312018557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5437
      · exact prime_fiftyFourAZ_14347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 312018557) ^ 156009278 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 57388 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 312018557) ^ 21748 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_356129471 : Nat.Prime 356129471 := by
  apply lucas_primality 356129471 (11 : ZMod 356129471)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (1548389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (1548389, 1)] : List FactorBlock).map factorBlockValue).prod) = 356129471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_1548389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 356129471) ^ 178064735 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 71225894 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 15483890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 356129471) ^ 230 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_404191789 : Nat.Prime 404191789 := by
  apply lucas_primality 404191789 (6 : ZMod 404191789)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (11, 2), (13, 1), (19, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 404191789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 404191789) ^ 202095894 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 134730596 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 57741684 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 36744708 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 31091676 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 21273252 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 404191789) ^ 17573556 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_407591837 : Nat.Prime 407591837 := by
  apply lucas_primality 407591837 (2 : ZMod 407591837)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (1922603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (1922603, 1)] : List FactorBlock).map factorBlockValue).prod) = 407591837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_1922603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 407591837) ^ 203795918 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 407591837) ^ 7690412 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 407591837) ^ 212 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_459237223 : Nat.Prime 459237223 := by
  apply lucas_primality 459237223 (5 : ZMod 459237223)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (8504393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (8504393, 1)] : List FactorBlock).map factorBlockValue).prod) = 459237223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_8504393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 459237223) ^ 229618611 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 459237223) ^ 153079074 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 459237223) ^ 54 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_481228519 : Nat.Prime 481228519 := by
  apply lucas_primality 481228519 (3 : ZMod 481228519)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (901177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (901177, 1)] : List FactorBlock).map factorBlockValue).prod) = 481228519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_89
      · exact prime_fiftyFourAZ_901177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 481228519) ^ 240614259 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 481228519) ^ 160409506 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 481228519) ^ 5407062 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 481228519) ^ 534 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_500000117 : Nat.Prime 500000117 := by
  apply lucas_primality 500000117 (2 : ZMod 500000117)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (31, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (31, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 500000117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 500000117) ^ 250000058 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 71428588 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 45454556 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 16129036 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 500000117) ^ 66836 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_501452533 : Nat.Prime 501452533 := by
  apply lucas_primality 501452533 (2 : ZMod 501452533)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (23, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (23, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) = 501452533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_9613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 501452533) ^ 250726266 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 501452533) ^ 167150844 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 501452533) ^ 71636076 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 501452533) ^ 21802284 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 501452533) ^ 52164 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_576021701 : Nat.Prime 576021701 := by
  apply lucas_primality 576021701 (2 : ZMod 576021701)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (5760217, 1)] : List FactorBlock).map factorBlockValue).prod) = 576021701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_5760217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 576021701) ^ 288010850 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 115204340 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 576021701) ^ 100 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_579178573 : Nat.Prime 579178573 := by
  apply lucas_primality 579178573 (14 : ZMod 579178573)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (6894983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (6894983, 1)] : List FactorBlock).map factorBlockValue).prod) = 579178573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_6894983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 579178573) ^ 289589286 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 193059524 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 82739796 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 579178573) ^ 84 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_614266579 : Nat.Prime 614266579 := by
  apply lucas_primality 614266579 (3 : ZMod 614266579)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (181, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (181, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod) = 614266579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_181
      · exact prime_fiftyFourAZ_6983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 614266579) ^ 307133289 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 204755526 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 3393738 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 614266579) ^ 87966 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_667351259 : Nat.Prime 667351259 := by
  apply lucas_primality 667351259 (2 : ZMod 667351259)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47667947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47667947, 1)] : List FactorBlock).map factorBlockValue).prod) = 667351259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_47667947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 667351259) ^ 333675629 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 667351259) ^ 95335894 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 667351259) ^ 14 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_756933791 : Nat.Prime 756933791 := by
  apply lucas_primality 756933791 (11 : ZMod 756933791)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 2), (55291, 1)] : List FactorBlock).map factorBlockValue).prod) = 756933791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_55291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 756933791) ^ 378466895 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 151386758 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 20457670 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 756933791) ^ 13690 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_961734911 : Nat.Prime 961734911 := by
  apply lucas_primality 961734911 (7 : ZMod 961734911)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1901, 1), (50591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1901, 1), (50591, 1)] : List FactorBlock).map factorBlockValue).prod) = 961734911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1901
      · exact prime_fiftyFourAZ_50591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 961734911) ^ 480867455 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 961734911) ^ 192346982 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 961734911) ^ 505910 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 961734911) ^ 19010 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_970780183 : Nat.Prime 970780183 := by
  apply lucas_primality 970780183 (5 : ZMod 970780183)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (7034639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (7034639, 1)] : List FactorBlock).map factorBlockValue).prod) = 970780183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_7034639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 970780183) ^ 485390091 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 970780183) ^ 323593394 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 970780183) ^ 42207834 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 970780183) ^ 138 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_990811369 : Nat.Prime 990811369 := by
  apply lucas_primality 990811369 (17 : ZMod 990811369)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (154621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (154621, 1)] : List FactorBlock).map factorBlockValue).prod) = 990811369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_89
      · exact prime_fiftyFourAZ_154621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 990811369) ^ 495405684 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 330270456 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 11132712 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (17 : ZMod 990811369) ^ 6408 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1078928387 : Nat.Prime 1078928387 := by
  apply lucas_primality 1078928387 (2 : ZMod 1078928387)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1399, 1), (385607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1078928387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1399
      · exact prime_fiftyFourAZ_385607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1078928387) ^ 539464193 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 771214 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1078928387) ^ 2798 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1088737823 : Nat.Prime 1088737823 := by
  apply lucas_primality 1088737823 (5 : ZMod 1088737823)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557, 1), (977323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557, 1), (977323, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088737823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_557
      · exact prime_fiftyFourAZ_977323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1088737823) ^ 544368911 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1088737823) ^ 1954646 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1088737823) ^ 1114 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1117022993 : Nat.Prime 1117022993 := by
  apply lucas_primality 1117022993 (3 : ZMod 1117022993)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (69813937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (69813937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1117022993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_69813937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1117022993) ^ 558511496 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1117022993) ^ 16 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1278561971 : Nat.Prime 1278561971 := by
  apply lucas_primality 1278561971 (2 : ZMod 1278561971)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2677, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2677, 1), (6823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1278561971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_2677
      · exact prime_fiftyFourAZ_6823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1278561971) ^ 639280985 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278561971) ^ 255712394 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278561971) ^ 182651710 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278561971) ^ 477610 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1278561971) ^ 187390 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1389114479 : Nat.Prime 1389114479 := by
  apply lucas_primality 1389114479 (7 : ZMod 1389114479)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5563, 1), (124853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5563, 1), (124853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1389114479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5563
      · exact prime_fiftyFourAZ_124853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1389114479) ^ 694557239 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1389114479) ^ 249706 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1389114479) ^ 11126 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1446324263 : Nat.Prime 1446324263 := by
  apply lucas_primality 1446324263 (5 : ZMod 1446324263)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (953, 1), (758827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (953, 1), (758827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1446324263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_953
      · exact prime_fiftyFourAZ_758827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1446324263) ^ 723162131 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1446324263) ^ 1517654 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1446324263) ^ 1906 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1513867583 : Nat.Prime 1513867583 := by
  apply lucas_primality 1513867583 (5 : ZMod 1513867583)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (756933791, 1)] : List FactorBlock).map factorBlockValue).prod) = 1513867583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_756933791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1513867583) ^ 756933791 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1513867583) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1621509367 : Nat.Prime 1621509367 := by
  apply lucas_primality 1621509367 (7 : ZMod 1621509367)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (739, 1), (365699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (739, 1), (365699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1621509367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_739
      · exact prime_fiftyFourAZ_365699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1621509367) ^ 810754683 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1621509367) ^ 540503122 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1621509367) ^ 2194194 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1621509367) ^ 4434 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1731666887 : Nat.Prime 1731666887 := by
  apply lucas_primality 1731666887 (5 : ZMod 1731666887)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (79, 1), (644701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731666887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_79
      · exact prime_fiftyFourAZ_644701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1731666887) ^ 865833443 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 101862758 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 21919834 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1731666887) ^ 2686 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1966233961 : Nat.Prime 1966233961 := by
  apply lucas_primality 1966233961 (7 : ZMod 1966233961)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (1153, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (1153, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1966233961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1153
      · exact prime_fiftyFourAZ_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1966233961) ^ 983116980 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 655411320 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 393246792 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 1705320 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966233961) ^ 1245240 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2086950601 : Nat.Prime 2086950601 := by
  apply lucas_primality 2086950601 (13 : ZMod 2086950601)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (7, 1), (17, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (7, 1), (17, 1), (9743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2086950601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_9743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2086950601) ^ 1043475300 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2086950601) ^ 695650200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2086950601) ^ 417390120 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2086950601) ^ 298135800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2086950601) ^ 122761800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2086950601) ^ 214200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2090736199 : Nat.Prime 2090736199 := by
  apply lucas_primality 2090736199 (15 : ZMod 2090736199)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1721, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1721, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2090736199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1721
      · exact prime_fiftyFourAZ_7499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 2090736199) ^ 1045368099 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 2090736199) ^ 696912066 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 2090736199) ^ 1214838 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 2090736199) ^ 278802 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2129671771 : Nat.Prime 2129671771 := by
  apply lucas_primality 2129671771 (22 : ZMod 2129671771)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (4175827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (4175827, 1)] : List FactorBlock).map factorBlockValue).prod) = 2129671771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_4175827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2129671771) ^ 1064835885 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 709890590 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 425934354 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 125274810 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2129671771) ^ 510 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2413359547 : Nat.Prime 2413359547 := by
  apply lucas_primality 2413359547 (2 : ZMod 2413359547)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (293, 1), (8123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (293, 1), (8123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2413359547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_293
      · exact prime_fiftyFourAZ_8123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2413359547) ^ 1206679773 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413359547) ^ 804453182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413359547) ^ 185643042 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413359547) ^ 8236722 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413359547) ^ 297102 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2431279603 : Nat.Prime 2431279603 := by
  apply lucas_primality 2431279603 (2 : ZMod 2431279603)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (283, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431279603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_239
      · exact prime_fiftyFourAZ_283
      · exact prime_fiftyFourAZ_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2431279603) ^ 1215639801 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 810426534 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 10172718 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 8591094 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2431279603) ^ 1217466 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2651438947 : Nat.Prime 2651438947 := by
  apply lucas_primality 2651438947 (3 : ZMod 2651438947)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (33992807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (33992807, 1)] : List FactorBlock).map factorBlockValue).prod) = 2651438947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_33992807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2651438947) ^ 1325719473 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 883812982 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 203956842 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2651438947) ^ 78 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2731329413 : Nat.Prime 2731329413 := by
  apply lucas_primality 2731329413 (2 : ZMod 2731329413)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (61, 1), (109, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (61, 1), (109, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 2731329413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_61
      · exact prime_fiftyFourAZ_109
      · exact prime_fiftyFourAZ_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2731329413) ^ 1365664706 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 390189916 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 160666436 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 44775892 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 25058068 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2731329413) ^ 3164924 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3130139557 : Nat.Prime 3130139557 := by
  apply lucas_primality 3130139557 (2 : ZMod 3130139557)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (569, 1), (152809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (569, 1), (152809, 1)] : List FactorBlock).map factorBlockValue).prod) = 3130139557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_569
      · exact prime_fiftyFourAZ_152809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3130139557) ^ 1565069778 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 1043379852 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 5501124 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3130139557) ^ 20484 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4004779187 : Nat.Prime 4004779187 := by
  apply lucas_primality 4004779187 (2 : ZMod 4004779187)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2551, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2551, 1), (27067, 1)] : List FactorBlock).map factorBlockValue).prod) = 4004779187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_2551
      · exact prime_fiftyFourAZ_27067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4004779187) ^ 2002389593 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 138095834 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 1569886 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4004779187) ^ 147958 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4368259799 : Nat.Prime 4368259799 := by
  apply lucas_primality 4368259799 (7 : ZMod 4368259799)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (312018557, 1)] : List FactorBlock).map factorBlockValue).prod) = 4368259799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_312018557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4368259799) ^ 2184129899 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 624037114 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4368259799) ^ 14 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4382406037 : Nat.Prime 4382406037 := by
  apply lucas_primality 4382406037 (6 : ZMod 4382406037)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (121733501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (121733501, 1)] : List FactorBlock).map factorBlockValue).prod) = 4382406037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_121733501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4382406037) ^ 2191203018 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4382406037) ^ 1460802012 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4382406037) ^ 36 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4610820719 : Nat.Prime 4610820719 := by
  apply lucas_primality 4610820719 (13 : ZMod 4610820719)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (23, 1), (292231, 1)] : List FactorBlock).map factorBlockValue).prod) = 4610820719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_292231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4610820719) ^ 2305410359 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 658688674 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 200470466 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4610820719) ^ 15778 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_5774742229 : Nat.Prime 5774742229 := by
  apply lucas_primality 5774742229 (19 : ZMod 5774742229)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (481228519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (481228519, 1)] : List FactorBlock).map factorBlockValue).prod) = 5774742229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_481228519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 5774742229) ^ 2887371114 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 5774742229) ^ 1924914076 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 5774742229) ^ 12 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_6103279213 : Nat.Prime 6103279213 := by
  apply lucas_primality 6103279213 (5 : ZMod 6103279213)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (311, 1), (1049, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (311, 1), (1049, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) = 6103279213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_311
      · exact prime_fiftyFourAZ_1049
      · exact prime_fiftyFourAZ_1559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6103279213) ^ 3051639606 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 2034426404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 19624692 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 5818188 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6103279213) ^ 3914868 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_89
      · exact prime_fiftyFourAZ_223
      · exact prime_fiftyFourAZ_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_6810796141 : Nat.Prime 6810796141 := by
  apply lucas_primality 6810796141 (2 : ZMod 6810796141)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1483, 1), (76543, 1)] : List FactorBlock).map factorBlockValue).prod) = 6810796141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1483
      · exact prime_fiftyFourAZ_76543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6810796141) ^ 3405398070 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 2270265380 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 1362159228 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 4592580 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6810796141) ^ 88980 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_7705406671 : Nat.Prime 7705406671 := by
  apply lucas_primality 7705406671 (6 : ZMod 7705406671)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (2383, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) = 7705406671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_2383
      · exact prime_fiftyFourAZ_8291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7705406671) ^ 3852703335 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 2568468890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 1541081334 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 592723590 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 3233490 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7705406671) ^ 929370 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1997
      · exact prime_fiftyFourAZ_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_8436948721 : Nat.Prime 8436948721 := by
  apply lucas_primality 8436948721 (7 : ZMod 8436948721)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (73, 1), (397, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 8436948721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_73
      · exact prime_fiftyFourAZ_397
      · exact prime_fiftyFourAZ_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8436948721) ^ 4218474360 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 2812316240 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 1687389744 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 115574640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 21251760 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8436948721) ^ 6955440 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_8487862729 : Nat.Prime 8487862729 := by
  apply lucas_primality 8487862729 (7 : ZMod 8487862729)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (7524701, 1)] : List FactorBlock).map factorBlockValue).prod) = 8487862729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_7524701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8487862729) ^ 4243931364 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 2829287576 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 180592824 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 8487862729) ^ 1128 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_9173293127 : Nat.Prime 9173293127 := by
  apply lucas_primality 9173293127 (5 : ZMod 9173293127)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (269802739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (269802739, 1)] : List FactorBlock).map factorBlockValue).prod) = 9173293127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_269802739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9173293127) ^ 4586646563 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9173293127) ^ 539605478 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9173293127) ^ 34 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_11120643179 : Nat.Prime 11120643179 := by
  apply lucas_primality 11120643179 (2 : ZMod 11120643179)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (55052689, 1)] : List FactorBlock).map factorBlockValue).prod) = 11120643179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_101
      · exact prime_fiftyFourAZ_55052689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11120643179) ^ 5560321589 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 110105378 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11120643179) ^ 202 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_15887027837 : Nat.Prime 15887027837 := by
  apply lucas_primality 15887027837 (2 : ZMod 15887027837)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3163, 1), (1255693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3163, 1), (1255693, 1)] : List FactorBlock).map factorBlockValue).prod) = 15887027837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3163
      · exact prime_fiftyFourAZ_1255693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15887027837) ^ 7943513918 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15887027837) ^ 5022772 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15887027837) ^ 12652 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_16767625597 : Nat.Prime 16767625597 := by
  apply lucas_primality 16767625597 (6 : ZMod 16767625597)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (127, 1), (186481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (127, 1), (186481, 1)] : List FactorBlock).map factorBlockValue).prod) = 16767625597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_127
      · exact prime_fiftyFourAZ_186481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16767625597) ^ 8383812798 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 5589208532 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 284197044 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 132028548 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 16767625597) ^ 89916 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_19471826177 : Nat.Prime 19471826177 := by
  apply lucas_primality 19471826177 (3 : ZMod 19471826177)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (11, 1), (6914711, 1)] : List FactorBlock).map factorBlockValue).prod) = 19471826177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_6914711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19471826177) ^ 9735913088 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 1770166016 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19471826177) ^ 2816 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_21580023643 : Nat.Prime 21580023643 := by
  apply lucas_primality 21580023643 (2 : ZMod 21580023643)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (127, 1), (193, 1), (7723, 1)] : List FactorBlock).map factorBlockValue).prod) = 21580023643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_127
      · exact prime_fiftyFourAZ_193
      · exact prime_fiftyFourAZ_7723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21580023643) ^ 10790011821 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 7193341214 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 1135790718 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 169921446 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 111813594 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21580023643) ^ 2794254 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_23752883989 : Nat.Prime 23752883989 := by
  apply lucas_primality 23752883989 (2 : ZMod 23752883989)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (219934111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (219934111, 1)] : List FactorBlock).map factorBlockValue).prod) = 23752883989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_219934111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23752883989) ^ 11876441994 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23752883989) ^ 7917627996 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23752883989) ^ 108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_26075531717 : Nat.Prime 26075531717 := by
  apply lucas_primality 26075531717 (2 : ZMod 26075531717)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (501452533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (501452533, 1)] : List FactorBlock).map factorBlockValue).prod) = 26075531717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_501452533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26075531717) ^ 13037765858 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 26075531717) ^ 2005810132 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 26075531717) ^ 52 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_29382133091 : Nat.Prime 29382133091 := by
  apply lucas_primality 29382133091 (2 : ZMod 29382133091)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (199, 1), (421, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (199, 1), (421, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 29382133091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_199
      · exact prime_fiftyFourAZ_421
      · exact prime_fiftyFourAZ_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29382133091) ^ 14691066545 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 5876426618 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 1728360770 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 147648910 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 69791290 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29382133091) ^ 14242430 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_71
      · exact prime_fiftyFourAZ_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_131
      · exact prime_fiftyFourAZ_149
      · exact prime_fiftyFourAZ_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_151
      · exact prime_fiftyFourAZ_479
      · exact prime_fiftyFourAZ_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_52419117589 : Nat.Prime 52419117589 := by
  apply lucas_primality 52419117589 (2 : ZMod 52419117589)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4368259799, 1)] : List FactorBlock).map factorBlockValue).prod) = 52419117589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_4368259799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52419117589) ^ 26209558794 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 17473039196 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 52419117589) ^ 12 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_52783422743 : Nat.Prime 52783422743 := by
  apply lucas_primality 52783422743 (5 : ZMod 52783422743)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1823, 1), (14477077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1823, 1), (14477077, 1)] : List FactorBlock).map factorBlockValue).prod) = 52783422743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1823
      · exact prime_fiftyFourAZ_14477077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52783422743) ^ 26391711371 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 52783422743) ^ 28954154 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 52783422743) ^ 3646 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_71580402031 : Nat.Prime 71580402031 := by
  apply lucas_primality 71580402031 (6 : ZMod 71580402031)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1031, 1), (2314271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1031, 1), (2314271, 1)] : List FactorBlock).map factorBlockValue).prod) = 71580402031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1031
      · exact prime_fiftyFourAZ_2314271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 71580402031) ^ 35790201015 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71580402031) ^ 23860134010 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71580402031) ^ 14316080406 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71580402031) ^ 69428130 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71580402031) ^ 30930 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_88088307689 : Nat.Prime 88088307689 := by
  apply lucas_primality 88088307689 (3 : ZMod 88088307689)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (541, 1), (20353121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (541, 1), (20353121, 1)] : List FactorBlock).map factorBlockValue).prod) = 88088307689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_541
      · exact prime_fiftyFourAZ_20353121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 88088307689) ^ 44044153844 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88088307689) ^ 162824968 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 88088307689) ^ 4328 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_103164566633 : Nat.Prime 103164566633 := by
  apply lucas_primality 103164566633 (3 : ZMod 103164566633)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (167, 1), (77218987, 1)] : List FactorBlock).map factorBlockValue).prod) = 103164566633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_167
      · exact prime_fiftyFourAZ_77218987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103164566633) ^ 51582283316 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 617751896 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 103164566633) ^ 1336 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_108998465977 : Nat.Prime 108998465977 := by
  apply lucas_primality 108998465977 (5 : ZMod 108998465977)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1513867583, 1)] : List FactorBlock).map factorBlockValue).prod) = 108998465977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1513867583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 108998465977) ^ 54499232988 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 36332821992 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 108998465977) ^ 72 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_112919378827 : Nat.Prime 112919378827 := by
  apply lucas_primality 112919378827 (14 : ZMod 112919378827)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19379, 1), (971149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19379, 1), (971149, 1)] : List FactorBlock).map factorBlockValue).prod) = 112919378827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19379
      · exact prime_fiftyFourAZ_971149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 112919378827) ^ 56459689413 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 112919378827) ^ 37639792942 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 112919378827) ^ 5826894 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 112919378827) ^ 116274 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_127269069457 : Nat.Prime 127269069457 := by
  apply lucas_primality 127269069457 (5 : ZMod 127269069457)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2651438947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2651438947, 1)] : List FactorBlock).map factorBlockValue).prod) = 127269069457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_2651438947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 127269069457) ^ 63634534728 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 127269069457) ^ 42423023152 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 127269069457) ^ 48 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_158313501439 : Nat.Prime 158313501439 := by
  apply lucas_primality 158313501439 (3 : ZMod 158313501439)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (246594239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (246594239, 1)] : List FactorBlock).map factorBlockValue).prod) = 158313501439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_107
      · exact prime_fiftyFourAZ_246594239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 158313501439) ^ 79156750719 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 52771167146 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 1479565434 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 158313501439) ^ 642 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_158997346943 : Nat.Prime 158997346943 := by
  apply lucas_primality 158997346943 (5 : ZMod 158997346943)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (8699, 1), (68713, 1)] : List FactorBlock).map factorBlockValue).prod) = 158997346943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_8699
      · exact prime_fiftyFourAZ_68713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158997346943) ^ 79498673471 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 22713906706 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 8368281418 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 18277658 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 158997346943) ^ 2313934 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_169787494937 : Nat.Prime 169787494937 := by
  apply lucas_primality 169787494937 (3 : ZMod 169787494937)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (1117022993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (1117022993, 1)] : List FactorBlock).map factorBlockValue).prod) = 169787494937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_1117022993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 169787494937) ^ 84893747468 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169787494937) ^ 8936183944 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 169787494937) ^ 152 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_184346679547 : Nat.Prime 184346679547 := by
  apply lucas_primality 184346679547 (2 : ZMod 184346679547)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3947, 1), (864917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3947, 1), (864917, 1)] : List FactorBlock).map factorBlockValue).prod) = 184346679547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_3947
      · exact prime_fiftyFourAZ_864917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184346679547) ^ 92173339773 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 61448893182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 46705518 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 184346679547) ^ 213138 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_194488996777 : Nat.Prime 194488996777 := by
  apply lucas_primality 194488996777 (7 : ZMod 194488996777)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6121, 1), (1323919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6121, 1), (1323919, 1)] : List FactorBlock).map factorBlockValue).prod) = 194488996777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_6121
      · exact prime_fiftyFourAZ_1323919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 194488996777) ^ 97244498388 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 64829665592 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 31774056 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 194488996777) ^ 146904 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_216104610427 : Nat.Prime 216104610427 := by
  apply lucas_primality 216104610427 (5 : ZMod 216104610427)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1217, 1), (29595263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1217, 1), (29595263, 1)] : List FactorBlock).map factorBlockValue).prod) = 216104610427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1217
      · exact prime_fiftyFourAZ_29595263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 216104610427) ^ 108052305213 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 72034870142 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 177571578 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 216104610427) ^ 7302 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_254818731547 : Nat.Prime 254818731547 := by
  apply lucas_primality 254818731547 (2 : ZMod 254818731547)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (12289, 1), (127997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (12289, 1), (127997, 1)] : List FactorBlock).map factorBlockValue).prod) = 254818731547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_12289
      · exact prime_fiftyFourAZ_127997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 254818731547) ^ 127409365773 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 84939577182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 20735514 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 254818731547) ^ 1990818 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_149
      · exact prime_fiftyFourAZ_1429
      · exact prime_fiftyFourAZ_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_295575079417 : Nat.Prime 295575079417 := by
  apply lucas_primality 295575079417 (10 : ZMod 295575079417)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (36107, 1), (341087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (36107, 1), (341087, 1)] : List FactorBlock).map factorBlockValue).prod) = 295575079417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_36107
      · exact prime_fiftyFourAZ_341087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 295575079417) ^ 147787539708 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 295575079417) ^ 98525026472 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 295575079417) ^ 8186088 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 295575079417) ^ 866568 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_400896468733 : Nat.Prime 400896468733 := by
  apply lucas_primality 400896468733 (5 : ZMod 400896468733)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (7159, 1), (113819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (7159, 1), (113819, 1)] : List FactorBlock).map factorBlockValue).prod) = 400896468733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_7159
      · exact prime_fiftyFourAZ_113819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 400896468733) ^ 200448234366 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 133632156244 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 9777962652 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 55998948 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 400896468733) ^ 3522228 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_500105447239 : Nat.Prime 500105447239 := by
  apply lucas_primality 500105447239 (3 : ZMod 500105447239)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (397, 1), (7239721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (397, 1), (7239721, 1)] : List FactorBlock).map factorBlockValue).prod) = 500105447239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_397
      · exact prime_fiftyFourAZ_7239721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 500105447239) ^ 250052723619 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 500105447239) ^ 166701815746 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 500105447239) ^ 17245015422 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 500105447239) ^ 1259711454 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 500105447239) ^ 69078 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_571933002133 : Nat.Prime 571933002133 := by
  apply lucas_primality 571933002133 (2 : ZMod 571933002133)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (15887027837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (15887027837, 1)] : List FactorBlock).map factorBlockValue).prod) = 571933002133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_15887027837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 571933002133) ^ 285966501066 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 571933002133) ^ 190644334044 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 571933002133) ^ 36 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_947671950089 : Nat.Prime 947671950089 := by
  apply lucas_primality 947671950089 (3 : ZMod 947671950089)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (34981, 1), (50543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (34981, 1), (50543, 1)] : List FactorBlock).map factorBlockValue).prod) = 947671950089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_67
      · exact prime_fiftyFourAZ_34981
      · exact prime_fiftyFourAZ_50543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 947671950089) ^ 473835975044 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 947671950089) ^ 14144357464 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 947671950089) ^ 27091048 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 947671950089) ^ 18749816 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1021310491259 : Nat.Prime 1021310491259 := by
  apply lucas_primality 1021310491259 (2 : ZMod 1021310491259)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (79, 1), (367, 1), (568163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (79, 1), (367, 1), (568163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1021310491259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_79
      · exact prime_fiftyFourAZ_367
      · exact prime_fiftyFourAZ_568163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1021310491259) ^ 510655245629 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1021310491259) ^ 32945499718 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1021310491259) ^ 12927980902 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1021310491259) ^ 2782862374 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1021310491259) ^ 1797566 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1432462387957 : Nat.Prime 1432462387957 := by
  apply lucas_primality 1432462387957 (7 : ZMod 1432462387957)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (1697, 1), (1496657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (1697, 1), (1496657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432462387957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_1697
      · exact prime_fiftyFourAZ_1496657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1432462387957) ^ 716231193978 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1432462387957) ^ 477487462652 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1432462387957) ^ 30477923148 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1432462387957) ^ 844114548 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1432462387957) ^ 957108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_35279
      · exact prime_fiftyFourAZ_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1895343900179 : Nat.Prime 1895343900179 := by
  apply lucas_primality 1895343900179 (2 : ZMod 1895343900179)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947671950089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947671950089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1895343900179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_947671950089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1895343900179) ^ 947671950089 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1895343900179) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_457
      · exact prime_fiftyFourAZ_1433
      · exact prime_fiftyFourAZ_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1911424697713 : Nat.Prime 1911424697713 := by
  apply lucas_primality 1911424697713 (5 : ZMod 1911424697713)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (337, 1), (39388079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (337, 1), (39388079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1911424697713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_337
      · exact prime_fiftyFourAZ_39388079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1911424697713) ^ 955712348856 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1911424697713) ^ 637141565904 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1911424697713) ^ 5671883376 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1911424697713) ^ 48528 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2215464064147 : Nat.Prime 2215464064147 := by
  apply lucas_primality 2215464064147 (2 : ZMod 2215464064147)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (2413359547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (2413359547, 1)] : List FactorBlock).map factorBlockValue).prod) = 2215464064147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_2413359547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2215464064147) ^ 1107732032073 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215464064147) ^ 738488021382 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215464064147) ^ 130321415538 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215464064147) ^ 918 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2244321898991 : Nat.Prime 2244321898991 := by
  apply lucas_primality 2244321898991 (7 : ZMod 2244321898991)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (29, 1), (229, 1), (1201, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (29, 1), (229, 1), (1201, 1), (1481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2244321898991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_229
      · exact prime_fiftyFourAZ_1201
      · exact prime_fiftyFourAZ_1481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2244321898991) ^ 1122160949495 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 448864379798 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 118122205210 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 77390410310 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 9800532310 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 1868710990 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2244321898991) ^ 1515409790 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2776281448651 : Nat.Prime 2776281448651 := by
  apply lucas_primality 2776281448651 (22 : ZMod 2776281448651)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (1088737823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (1088737823, 1)] : List FactorBlock).map factorBlockValue).prod) = 2776281448651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_1088737823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2776281448651) ^ 1388140724325 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 925427149550 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 555256289730 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 163310673450 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (22 : ZMod 2776281448651) ^ 2550 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3167005364581 : Nat.Prime 3167005364581 := by
  apply lucas_primality 3167005364581 (6 : ZMod 3167005364581)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (52783422743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (52783422743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3167005364581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_52783422743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3167005364581) ^ 1583502682290 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3167005364581) ^ 1055668454860 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3167005364581) ^ 633401072916 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3167005364581) ^ 60 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3790687800359 : Nat.Prime 3790687800359 := by
  apply lucas_primality 3790687800359 (11 : ZMod 3790687800359)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1895343900179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1895343900179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3790687800359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1895343900179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 3790687800359) ^ 1895343900179 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3790687800359) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4488643797983 : Nat.Prime 4488643797983 := by
  apply lucas_primality 4488643797983 (5 : ZMod 4488643797983)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2244321898991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2244321898991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4488643797983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_2244321898991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4488643797983) ^ 2244321898991 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4488643797983) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4507311568399 : Nat.Prime 4507311568399 := by
  apply lucas_primality 4507311568399 (3 : ZMod 4507311568399)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4877, 1), (154032929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4877, 1), (154032929, 1)] : List FactorBlock).map factorBlockValue).prod) = 4507311568399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_4877
      · exact prime_fiftyFourAZ_154032929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4507311568399) ^ 2253655784199 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4507311568399) ^ 1502437189466 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4507311568399) ^ 924197574 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4507311568399) ^ 29262 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_6857614732721 : Nat.Prime 6857614732721 := by
  apply lucas_primality 6857614732721 (3 : ZMod 6857614732721)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (41, 1), (2090736199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (41, 1), (2090736199, 1)] : List FactorBlock).map factorBlockValue).prod) = 6857614732721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_2090736199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6857614732721) ^ 3428807366360 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6857614732721) ^ 1371522946544 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6857614732721) ^ 167258895920 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6857614732721) ^ 3280 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_12469425776321 : Nat.Prime 12469425776321 := by
  apply lucas_primality 12469425776321 (3 : ZMod 12469425776321)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (163, 1), (239061077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (163, 1), (239061077, 1)] : List FactorBlock).map factorBlockValue).prod) = 12469425776321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_163
      · exact prime_fiftyFourAZ_239061077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12469425776321) ^ 6234712888160 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 2493885155264 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 76499544640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12469425776321) ^ 52160 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_14287533837817 : Nat.Prime 14287533837817 := by
  apply lucas_primality 14287533837817 (5 : ZMod 14287533837817)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (619, 1), (961734911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (619, 1), (961734911, 1)] : List FactorBlock).map factorBlockValue).prod) = 14287533837817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_619
      · exact prime_fiftyFourAZ_961734911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14287533837817) ^ 7143766918908 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14287533837817) ^ 4762511279272 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14287533837817) ^ 23081637864 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14287533837817) ^ 14856 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_14781163755053 : Nat.Prime 14781163755053 := by
  apply lucas_primality 14781163755053 (2 : ZMod 14781163755053)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (194488996777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (194488996777, 1)] : List FactorBlock).map factorBlockValue).prod) = 14781163755053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_194488996777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14781163755053) ^ 7390581877526 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14781163755053) ^ 777955987108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14781163755053) ^ 76 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_14820266192971 : Nat.Prime 14820266192971 := by
  apply lucas_primality 14820266192971 (3 : ZMod 14820266192971)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (9281, 1), (7603997, 1)] : List FactorBlock).map factorBlockValue).prod) = 14820266192971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_9281
      · exact prime_fiftyFourAZ_7603997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14820266192971) ^ 7410133096485 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 4940088730990 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2964053238594 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 2117180884710 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1596839370 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14820266192971) ^ 1949010 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_15003163417171 : Nat.Prime 15003163417171 := by
  apply lucas_primality 15003163417171 (10 : ZMod 15003163417171)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (500105447239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (500105447239, 1)] : List FactorBlock).map factorBlockValue).prod) = 15003163417171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_500105447239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 15003163417171) ^ 7501581708585 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15003163417171) ^ 5001054472390 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15003163417171) ^ 3000632683434 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 15003163417171) ^ 30 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_19946477413151 : Nat.Prime 19946477413151 := by
  apply lucas_primality 19946477413151 (11 : ZMod 19946477413151)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (8487862729, 1)] : List FactorBlock).map factorBlockValue).prod) = 19946477413151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_8487862729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 19946477413151) ^ 9973238706575 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 3989295482630 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 424393136450 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 19946477413151) ^ 2350 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_21992409443029 : Nat.Prime 21992409443029 := by
  apply lucas_primality 21992409443029 (2 : ZMod 21992409443029)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (547, 1), (77917639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (547, 1), (77917639, 1)] : List FactorBlock).map factorBlockValue).prod) = 21992409443029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_547
      · exact prime_fiftyFourAZ_77917639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21992409443029) ^ 10996204721514 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21992409443029) ^ 7330803147676 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21992409443029) ^ 511451382396 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21992409443029) ^ 40205501724 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21992409443029) ^ 282252 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_28544129406473 : Nat.Prime 28544129406473 := by
  apply lucas_primality 28544129406473 (3 : ZMod 28544129406473)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3307, 1), (1078928387, 1)] : List FactorBlock).map factorBlockValue).prod) = 28544129406473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3307
      · exact prime_fiftyFourAZ_1078928387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28544129406473) ^ 14272064703236 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 8631427096 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 28544129406473) ^ 26456 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_42992720020091 : Nat.Prime 42992720020091 := by
  apply lucas_primality 42992720020091 (2 : ZMod 42992720020091)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (181, 1), (23752883989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (181, 1), (23752883989, 1)] : List FactorBlock).map factorBlockValue).prod) = 42992720020091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_181
      · exact prime_fiftyFourAZ_23752883989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42992720020091) ^ 21496360010045 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42992720020091) ^ 8598544004018 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42992720020091) ^ 237528839890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42992720020091) ^ 1810 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_45989776525361 : Nat.Prime 45989776525361 := by
  apply lucas_primality 45989776525361 (6 : ZMod 45989776525361)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (179, 1), (188916269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (179, 1), (188916269, 1)] : List FactorBlock).map factorBlockValue).prod) = 45989776525361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_179
      · exact prime_fiftyFourAZ_188916269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45989776525361) ^ 22994888262680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 9197955305072 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 2705280972080 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 256926125840 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 45989776525361) ^ 243440 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_57298495518281 : Nat.Prime 57298495518281 := by
  apply lucas_primality 57298495518281 (3 : ZMod 57298495518281)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1432462387957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1432462387957, 1)] : List FactorBlock).map factorBlockValue).prod) = 57298495518281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1432462387957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 57298495518281) ^ 28649247759140 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298495518281) ^ 11459699103656 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298495518281) ^ 40 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_70909951668091 : Nat.Prime 70909951668091 := by
  apply lucas_primality 70909951668091 (10 : ZMod 70909951668091)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1032763, 1), (2288681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1032763, 1), (2288681, 1)] : List FactorBlock).map factorBlockValue).prod) = 70909951668091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1032763
      · exact prime_fiftyFourAZ_2288681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 70909951668091) ^ 35454975834045 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 23636650556030 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 14181990333618 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 68660430 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 70909951668091) ^ 30982890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_82294473700337 : Nat.Prime 82294473700337 := by
  apply lucas_primality 82294473700337 (3 : ZMod 82294473700337)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (683, 1), (787, 1), (2713, 1), (3527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (683, 1), (787, 1), (2713, 1), (3527, 1)] : List FactorBlock).map factorBlockValue).prod) = 82294473700337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_683
      · exact prime_fiftyFourAZ_787
      · exact prime_fiftyFourAZ_2713
      · exact prime_fiftyFourAZ_3527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82294473700337) ^ 41147236850168 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82294473700337) ^ 120489712592 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82294473700337) ^ 104567310928 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82294473700337) ^ 30333385072 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82294473700337) ^ 23332711568 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_104948605941079 : Nat.Prime 104948605941079 := by
  apply lucas_primality 104948605941079 (3 : ZMod 104948605941079)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 2), (14143, 1), (76679, 1)] : List FactorBlock).map factorBlockValue).prod) = 104948605941079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_127
      · exact prime_fiftyFourAZ_14143
      · exact prime_fiftyFourAZ_76679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104948605941079) ^ 52474302970539 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 34982868647026 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 826366975914 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 7420533546 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 104948605941079) ^ 1368674682 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_107022411157729 : Nat.Prime 107022411157729 := by
  apply lucas_primality 107022411157729 (19 : ZMod 107022411157729)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (47, 1), (8171, 1), (263899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (47, 1), (8171, 1), (263899, 1)] : List FactorBlock).map factorBlockValue).prod) = 107022411157729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_8171
      · exact prime_fiftyFourAZ_263899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 107022411157729) ^ 53511205578864 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 35674137052576 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 9729310105248 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 2277072577824 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 13097835168 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 107022411157729) ^ 405543072 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_130648343779361 : Nat.Prime 130648343779361 := by
  apply lucas_primality 130648343779361 (3 : ZMod 130648343779361)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (31, 2), (977, 1), (79063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (31, 2), (977, 1), (79063, 1)] : List FactorBlock).map factorBlockValue).prod) = 130648343779361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_977
      · exact prime_fiftyFourAZ_79063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130648343779361) ^ 65324171889680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130648343779361) ^ 26129668755872 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130648343779361) ^ 11877122161760 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130648343779361) ^ 4214462702560 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130648343779361) ^ 133723995680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130648343779361) ^ 1652458720 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_131595537606037 : Nat.Prime 131595537606037 := by
  apply lucas_primality 131595537606037 (2 : ZMod 131595537606037)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (83, 1), (356129471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (83, 1), (356129471, 1)] : List FactorBlock).map factorBlockValue).prod) = 131595537606037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_83
      · exact prime_fiftyFourAZ_356129471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131595537606037) ^ 65797768803018 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 43865179202012 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 18799362515148 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 2482934671812 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 1585488404892 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 131595537606037) ^ 369516 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_144165029076967 : Nat.Prime 144165029076967 := by
  apply lucas_primality 144165029076967 (47 : ZMod 144165029076967)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (463, 1), (2731329413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (463, 1), (2731329413, 1)] : List FactorBlock).map factorBlockValue).prod) = 144165029076967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_463
      · exact prime_fiftyFourAZ_2731329413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (47 : ZMod 144165029076967) ^ 72082514538483 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 48055009692322 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 7587633109314 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 311371553082 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (47 : ZMod 144165029076967) ^ 52782 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_161735950924213 : Nat.Prime 161735950924213 := by
  apply lucas_primality 161735950924213 (2 : ZMod 161735950924213)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (43, 1), (47, 1), (79, 1), (877, 1), (13751, 1)] : List FactorBlock).map factorBlockValue).prod) = 161735950924213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_79
      · exact prime_fiftyFourAZ_877
      · exact prime_fiftyFourAZ_13751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161735950924213) ^ 80867975462106 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 53911983641404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 23105135846316 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3761301184284 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 3441190445196 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 2047290518028 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 184419556356 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 161735950924213) ^ 11761759212 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_171751255104959 : Nat.Prime 171751255104959 := by
  apply lucas_primality 171751255104959 (31 : ZMod 171751255104959)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (73, 1), (1607, 1), (43060817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (73, 1), (1607, 1), (43060817, 1)] : List FactorBlock).map factorBlockValue).prod) = 171751255104959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_73
      · exact prime_fiftyFourAZ_1607
      · exact prime_fiftyFourAZ_43060817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 171751255104959) ^ 85875627552479 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (31 : ZMod 171751255104959) ^ 10103015006174 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (31 : ZMod 171751255104959) ^ 2352756919246 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (31 : ZMod 171751255104959) ^ 106876947794 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (31 : ZMod 171751255104959) ^ 3988574 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_197212046147609 : Nat.Prime 197212046147609 := by
  apply lucas_primality 197212046147609 (3 : ZMod 197212046147609)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (1049, 1), (500000117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (1049, 1), (500000117, 1)] : List FactorBlock).map factorBlockValue).prod) = 197212046147609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_1049
      · exact prime_fiftyFourAZ_500000117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 197212046147609) ^ 98606023073804 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 4196000981864 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 188000043992 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 197212046147609) ^ 394424 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_197901371804377 : Nat.Prime 197901371804377 := by
  apply lucas_primality 197901371804377 (5 : ZMod 197901371804377)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 2), (41, 1), (209281249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 2), (41, 1), (209281249, 1)] : List FactorBlock).map factorBlockValue).prod) = 197901371804377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_209281249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 197901371804377) ^ 98950685902188 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 65967123934792 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 6383915219496 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 4826862726936 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 197901371804377) ^ 945624 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_211161009607909 : Nat.Prime 211161009607909 := by
  apply lucas_primality 211161009607909 (2 : ZMod 211161009607909)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79, 1), (89, 1), (761, 1), (1741, 1), (1889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79, 1), (89, 1), (761, 1), (1741, 1), (1889, 1)] : List FactorBlock).map factorBlockValue).prod) = 211161009607909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_79
      · exact prime_fiftyFourAZ_89
      · exact prime_fiftyFourAZ_761
      · exact prime_fiftyFourAZ_1741
      · exact prime_fiftyFourAZ_1889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211161009607909) ^ 105580504803954 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 70387003202636 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 2672924172252 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 2372595613572 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 277478330628 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 121287196788 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 211161009607909) ^ 111784547172 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_219924094430291 : Nat.Prime 219924094430291 := by
  apply lucas_primality 219924094430291 (2 : ZMod 219924094430291)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21992409443029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21992409443029, 1)] : List FactorBlock).map factorBlockValue).prod) = 219924094430291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_21992409443029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219924094430291) ^ 109962047215145 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 219924094430291) ^ 43984818886058 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 219924094430291) ^ 10 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_302303849620517 : Nat.Prime 302303849620517 := by
  apply lucas_primality 302303849620517 (2 : ZMod 302303849620517)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (443, 1), (4610820719, 1)] : List FactorBlock).map factorBlockValue).prod) = 302303849620517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_443
      · exact prime_fiftyFourAZ_4610820719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302303849620517) ^ 151151924810258 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 8170374314068 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 682401466412 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 302303849620517) ^ 65564 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_310521788772829 : Nat.Prime 310521788772829 := by
  apply lucas_primality 310521788772829 (2 : ZMod 310521788772829)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (547, 1), (1278561971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (547, 1), (1278561971, 1)] : List FactorBlock).map factorBlockValue).prod) = 310521788772829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_547
      · exact prime_fiftyFourAZ_1278561971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 310521788772829) ^ 155260894386414 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 310521788772829) ^ 103507262924276 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 310521788772829) ^ 8392480777644 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 310521788772829) ^ 567681515124 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 310521788772829) ^ 242868 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_374142517230199 : Nat.Prime 374142517230199 := by
  apply lucas_primality 374142517230199 (6 : ZMod 374142517230199)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (79, 1), (1091, 1), (12262583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (79, 1), (1091, 1), (12262583, 1)] : List FactorBlock).map factorBlockValue).prod) = 374142517230199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_79
      · exact prime_fiftyFourAZ_1091
      · exact prime_fiftyFourAZ_12262583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 374142517230199) ^ 187071258615099 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 374142517230199) ^ 124714172410066 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 374142517230199) ^ 6341398597122 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 374142517230199) ^ 4735981230762 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 374142517230199) ^ 342935396178 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 374142517230199) ^ 30510906 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_402858330250993 : Nat.Prime 402858330250993 := by
  apply lucas_primality 402858330250993 (5 : ZMod 402858330250993)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (108998465977, 1)] : List FactorBlock).map factorBlockValue).prod) = 402858330250993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_108998465977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402858330250993) ^ 201429165125496 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 134286110083664 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 57551190035856 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 36623484568272 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 402858330250993) ^ 3696 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_676997700942263 : Nat.Prime 676997700942263 := by
  apply lucas_primality 676997700942263 (5 : ZMod 676997700942263)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (541, 1), (1123, 1), (79594331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (541, 1), (1123, 1), (79594331, 1)] : List FactorBlock).map factorBlockValue).prod) = 676997700942263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_541
      · exact prime_fiftyFourAZ_1123
      · exact prime_fiftyFourAZ_79594331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 676997700942263) ^ 338498850471131 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 96713957277466 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 1251382071982 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 602847462994 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 676997700942263) ^ 8505602 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_695686433921251 : Nat.Prime 695686433921251 := by
  apply lucas_primality 695686433921251 (13 : ZMod 695686433921251)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (7907, 1), (23462297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (7907, 1), (23462297, 1)] : List FactorBlock).map factorBlockValue).prod) = 695686433921251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7907
      · exact prime_fiftyFourAZ_23462297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 695686433921251) ^ 347843216960625 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 231895477973750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 139137286784250 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 87983613750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 695686433921251) ^ 29651250 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_716131620214481 : Nat.Prime 716131620214481 := by
  apply lucas_primality 716131620214481 (3 : ZMod 716131620214481)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (41, 1), (1117, 1), (5443, 1), (35911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (41, 1), (1117, 1), (5443, 1), (35911, 1)] : List FactorBlock).map factorBlockValue).prod) = 716131620214481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_1117
      · exact prime_fiftyFourAZ_5443
      · exact prime_fiftyFourAZ_35911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 716131620214481) ^ 358065810107240 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 716131620214481) ^ 143226324042896 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 716131620214481) ^ 17466624883280 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 716131620214481) ^ 641120519440 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 716131620214481) ^ 131569285360 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 716131620214481) ^ 19941845680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_791051220811877 : Nat.Prime 791051220811877 := by
  apply lucas_primality 791051220811877 (2 : ZMod 791051220811877)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (347, 1), (109481, 1), (5205667, 1)] : List FactorBlock).map factorBlockValue).prod) = 791051220811877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_347
      · exact prime_fiftyFourAZ_109481
      · exact prime_fiftyFourAZ_5205667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 791051220811877) ^ 395525610405938 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 2279686515308 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 7225465796 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 791051220811877) ^ 151959628 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_944302595030827 : Nat.Prime 944302595030827 := by
  apply lucas_primality 944302595030827 (2 : ZMod 944302595030827)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5701, 1), (43541, 1), (634031, 1)] : List FactorBlock).map factorBlockValue).prod) = 944302595030827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5701
      · exact prime_fiftyFourAZ_43541
      · exact prime_fiftyFourAZ_634031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 944302595030827) ^ 472151297515413 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 314767531676942 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 165638062626 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 21687664386 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 944302595030827) ^ 1489363446 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1230821229214301 : Nat.Prime 1230821229214301 := by
  apply lucas_primality 1230821229214301 (2 : ZMod 1230821229214301)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (109, 1), (112919378827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (109, 1), (112919378827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1230821229214301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_109
      · exact prime_fiftyFourAZ_112919378827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1230821229214301) ^ 615410614607150 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230821229214301) ^ 246164245842860 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230821229214301) ^ 11291937882700 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1230821229214301) ^ 10900 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1282642029276763 : Nat.Prime 1282642029276763 := by
  apply lucas_primality 1282642029276763 (3 : ZMod 1282642029276763)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (2776281448651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (2776281448651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1282642029276763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_2776281448651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1282642029276763) ^ 641321014638381 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 427547343092254 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 183234575610966 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 116603820843342 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282642029276763) ^ 462 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1659615521571361 : Nat.Prime 1659615521571361 := by
  apply lucas_primality 1659615521571361 (19 : ZMod 1659615521571361)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (137, 1), (229, 1), (761, 1), (16091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (137, 1), (229, 1), (761, 1), (16091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1659615521571361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_137
      · exact prime_fiftyFourAZ_229
      · exact prime_fiftyFourAZ_761
      · exact prime_fiftyFourAZ_16091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1659615521571361) ^ 829807760785680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 553205173857120 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 331923104314272 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 12113981909280 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 7247229351840 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 2180835113760 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659615521571361) ^ 103139364960 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1757917504040977 : Nat.Prime 1757917504040977 := by
  apply lucas_primality 1757917504040977 (5 : ZMod 1757917504040977)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (394819, 1), (30919891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (394819, 1), (30919891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1757917504040977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_394819
      · exact prime_fiftyFourAZ_30919891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1757917504040977) ^ 878958752020488 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1757917504040977) ^ 585972501346992 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1757917504040977) ^ 4452464304 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1757917504040977) ^ 56853936 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2461642458428603 : Nat.Prime 2461642458428603 := by
  apply lucas_primality 2461642458428603 (2 : ZMod 2461642458428603)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1230821229214301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1230821229214301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2461642458428603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1230821229214301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2461642458428603) ^ 1230821229214301 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2461642458428603) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2879936805405053 : Nat.Prime 2879936805405053 := by
  apply lucas_primality 2879936805405053 (2 : ZMod 2879936805405053)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (61, 1), (67, 1), (463, 1), (20025517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2879936805405053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_61
      · exact prime_fiftyFourAZ_67
      · exact prime_fiftyFourAZ_463
      · exact prime_fiftyFourAZ_20025517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2879936805405053) ^ 1439968402702526 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 151575621337108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 47212078777132 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 42984131423956 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 6220165886404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2879936805405053) ^ 143813356 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3139854234712031 : Nat.Prime 3139854234712031 := by
  apply lucas_primality 3139854234712031 (7 : ZMod 3139854234712031)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (28544129406473, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139854234712031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_28544129406473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3139854234712031) ^ 1569927117356015 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 627970846942406 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 285441294064730 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3139854234712031) ^ 110 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4345662143985583 : Nat.Prime 4345662143985583 := by
  apply lucas_primality 4345662143985583 (3 : ZMod 4345662143985583)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (14781163755053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (14781163755053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4345662143985583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_14781163755053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4345662143985583) ^ 2172831071992791 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 1448554047995194 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 620808877712226 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4345662143985583) ^ 294 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_5759873610810107 : Nat.Prime 5759873610810107 := by
  apply lucas_primality 5759873610810107 (2 : ZMod 5759873610810107)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2879936805405053, 1)] : List FactorBlock).map factorBlockValue).prod) = 5759873610810107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_2879936805405053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5759873610810107) ^ 2879936805405053 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759873610810107) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_11176723056977671 : Nat.Prime 11176723056977671 := by
  apply lucas_primality 11176723056977671 (3 : ZMod 11176723056977671)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (4488643797983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (4488643797983, 1)] : List FactorBlock).map factorBlockValue).prod) = 11176723056977671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_83
      · exact prime_fiftyFourAZ_4488643797983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11176723056977671) ^ 5588361528488835 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 3725574352325890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 2235344611395534 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 134659313939490 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11176723056977671) ^ 2490 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_81047
      · exact prime_fiftyFourAZ_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_13200878061346993 : Nat.Prime 13200878061346993 := by
  apply lucas_primality 13200878061346993 (5 : ZMod 13200878061346993)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (137, 1), (4933, 1), (21417871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (137, 1), (4933, 1), (21417871, 1)] : List FactorBlock).map factorBlockValue).prod) = 13200878061346993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_137
      · exact prime_fiftyFourAZ_4933
      · exact prime_fiftyFourAZ_21417871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13200878061346993) ^ 6600439030673496 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 4400292687115664 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 694783055860368 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 96356774170416 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 2676034474224 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13200878061346993) ^ 616348752 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_13372745926364969 : Nat.Prime 13372745926364969 := by
  apply lucas_primality 13372745926364969 (3 : ZMod 13372745926364969)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (223, 1), (52419117589, 1)] : List FactorBlock).map factorBlockValue).prod) = 13372745926364969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_223
      · exact prime_fiftyFourAZ_52419117589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13372745926364969) ^ 6686372963182484 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1215704175124088 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 1028672763566536 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 59967470521816 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13372745926364969) ^ 255112 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_26507396322160213 : Nat.Prime 26507396322160213 := by
  apply lucas_primality 26507396322160213 (5 : ZMod 26507396322160213)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5237, 1), (63487, 1), (6643829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5237, 1), (63487, 1), (6643829, 1)] : List FactorBlock).map factorBlockValue).prod) = 26507396322160213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5237
      · exact prime_fiftyFourAZ_63487
      · exact prime_fiftyFourAZ_6643829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26507396322160213) ^ 13253698161080106 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 26507396322160213) ^ 8835798774053404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 26507396322160213) ^ 5061561260676 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 26507396322160213) ^ 417524789676 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 26507396322160213) ^ 3989777028 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_34548999256651933 : Nat.Prime 34548999256651933 := by
  apply lucas_primality 34548999256651933 (5 : ZMod 34548999256651933)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (31, 1), (191, 1), (1187, 1), (1453, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (31, 1), (191, 1), (1187, 1), (1453, 1), (7229, 1)] : List FactorBlock).map factorBlockValue).prod) = 34548999256651933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_191
      · exact prime_fiftyFourAZ_1187
      · exact prime_fiftyFourAZ_1453
      · exact prime_fiftyFourAZ_7229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34548999256651933) ^ 17274499628325966 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 11516333085550644 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 2657615327434764 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 1114483846988772 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 180884812862052 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 29106149331636 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 23777700796044 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34548999256651933) ^ 4779222472908 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_34600664721388751 : Nat.Prime 34600664721388751 := by
  apply lucas_primality 34600664721388751 (13 : ZMod 34600664721388751)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (233, 1), (881, 1), (8741, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (233, 1), (881, 1), (8741, 1), (15427, 1)] : List FactorBlock).map factorBlockValue).prod) = 34600664721388751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_233
      · exact prime_fiftyFourAZ_881
      · exact prime_fiftyFourAZ_8741
      · exact prime_fiftyFourAZ_15427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 34600664721388751) ^ 17300332360694375 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 6920132944277750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 148500706958750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 39274307288750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 3958433213750 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 34600664721388751) ^ 2242864116250 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_50582541718966931 : Nat.Prime 50582541718966931 := by
  apply lucas_primality 50582541718966931 (2 : ZMod 50582541718966931)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (219924094430291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (219924094430291, 1)] : List FactorBlock).map factorBlockValue).prod) = 50582541718966931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_219924094430291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50582541718966931) ^ 25291270859483465 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 50582541718966931) ^ 10116508343793386 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 50582541718966931) ^ 2199240944302910 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 50582541718966931) ^ 230 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_56140086323316791 : Nat.Prime 56140086323316791 := by
  apply lucas_primality 56140086323316791 (11 : ZMod 56140086323316791)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1481, 1), (3790687800359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1481, 1), (3790687800359, 1)] : List FactorBlock).map factorBlockValue).prod) = 56140086323316791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_1481
      · exact prime_fiftyFourAZ_3790687800359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 56140086323316791) ^ 28070043161658395 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56140086323316791) ^ 11228017264663358 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56140086323316791) ^ 37906878003590 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 56140086323316791) ^ 14810 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_60698918627885897 : Nat.Prime 60698918627885897 := by
  apply lucas_primality 60698918627885897 (3 : ZMod 60698918627885897)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (70909951668091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (70909951668091, 1)] : List FactorBlock).map factorBlockValue).prod) = 60698918627885897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_107
      · exact prime_fiftyFourAZ_70909951668091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60698918627885897) ^ 30349459313942948 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60698918627885897) ^ 567279613344728 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60698918627885897) ^ 856 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_69201329442777503 : Nat.Prime 69201329442777503 := by
  apply lucas_primality 69201329442777503 (5 : ZMod 69201329442777503)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34600664721388751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34600664721388751, 1)] : List FactorBlock).map factorBlockValue).prod) = 69201329442777503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_34600664721388751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 69201329442777503) ^ 34600664721388751 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 69201329442777503) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_78531733309302509 : Nat.Prime 78531733309302509 := by
  apply lucas_primality 78531733309302509 (2 : ZMod 78531733309302509)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (676997700942263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (676997700942263, 1)] : List FactorBlock).map factorBlockValue).prod) = 78531733309302509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_676997700942263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78531733309302509) ^ 39265866654651254 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 78531733309302509) ^ 2707990803769052 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 78531733309302509) ^ 116 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_87849902605848473 : Nat.Prime 87849902605848473 := by
  apply lucas_primality 87849902605848473 (3 : ZMod 87849902605848473)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (31, 1), (2431189, 1), (5024269, 1)] : List FactorBlock).map factorBlockValue).prod) = 87849902605848473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_2431189
      · exact prime_fiftyFourAZ_5024269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87849902605848473) ^ 43924951302924236 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 3029306986408568 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 2833867825995112 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 36134542648 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 87849902605848473) ^ 17485111288 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_99668269744904299 : Nat.Prime 99668269744904299 := by
  apply lucas_primality 99668269744904299 (2 : ZMod 99668269744904299)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (47, 1), (73, 1), (254818731547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (47, 1), (73, 1), (254818731547, 1)] : List FactorBlock).map factorBlockValue).prod) = 99668269744904299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_73
      · exact prime_fiftyFourAZ_254818731547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 99668269744904299) ^ 49834134872452149 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 33222756581634766 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 5245698407626542 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 2120601483934134 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 1365318763628826 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 99668269744904299) ^ 391134 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_135981455480185333 : Nat.Prime 135981455480185333 := by
  apply lucas_primality 135981455480185333 (6 : ZMod 135981455480185333)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (471217, 1), (407591837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (471217, 1), (407591837, 1)] : List FactorBlock).map factorBlockValue).prod) = 135981455480185333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_471217
      · exact prime_fiftyFourAZ_407591837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 135981455480185333) ^ 67990727740092666 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 45327151826728444 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 2304770431867548 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 288575020596 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 135981455480185333) ^ 333621636 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_265073963221602131 : Nat.Prime 265073963221602131 := by
  apply lucas_primality 265073963221602131 (2 : ZMod 265073963221602131)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26507396322160213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26507396322160213, 1)] : List FactorBlock).map factorBlockValue).prod) = 265073963221602131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_26507396322160213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 265073963221602131) ^ 132536981610801065 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 265073963221602131) ^ 53014792644320426 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 265073963221602131) ^ 10 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_443794142129759999 : Nat.Prime 443794142129759999 := by
  apply lucas_primality 443794142129759999 (7 : ZMod 443794142129759999)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (1282642029276763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (1282642029276763, 1)] : List FactorBlock).map factorBlockValue).prod) = 443794142129759999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_173
      · exact prime_fiftyFourAZ_1282642029276763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 443794142129759999) ^ 221897071064879999 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 443794142129759999) ^ 2565284058553526 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (7 : ZMod 443794142129759999) ^ 346 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_61717
      · exact prime_fiftyFourAZ_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1064113857573247303 : Nat.Prime 1064113857573247303 := by
  apply lucas_primality 1064113857573247303 (3 : ZMod 1064113857573247303)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (769, 1), (115001, 1), (28245583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (769, 1), (115001, 1), (28245583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1064113857573247303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_71
      · exact prime_fiftyFourAZ_769
      · exact prime_fiftyFourAZ_115001
      · exact prime_fiftyFourAZ_28245583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1064113857573247303) ^ 532056928786623651 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064113857573247303) ^ 354704619191082434 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064113857573247303) ^ 14987519120749962 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064113857573247303) ^ 1383763143788358 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064113857573247303) ^ 9253083517302 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1064113857573247303) ^ 37673637594 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1093873445440084147 : Nat.Prime 1093873445440084147 := by
  apply lucas_primality 1093873445440084147 (5 : ZMod 1093873445440084147)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (11821, 1), (158997346943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1093873445440084147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_97
      · exact prime_fiftyFourAZ_11821
      · exact prime_fiftyFourAZ_158997346943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1093873445440084147) ^ 546936722720042073 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 364624481813361382 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 11277045829279218 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 92536455920826 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1093873445440084147) ^ 6879822 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2120591705772817049 : Nat.Prime 2120591705772817049 := by
  apply lucas_primality 2120591705772817049 (3 : ZMod 2120591705772817049)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (265073963221602131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (265073963221602131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2120591705772817049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_265073963221602131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2120591705772817049) ^ 1060295852886408524 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2120591705772817049) ^ 8 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3956052268000347139 : Nat.Prime 3956052268000347139 := by
  apply lucas_primality 3956052268000347139 (2 : ZMod 3956052268000347139)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (587, 1), (2215464064147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (587, 1), (2215464064147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3956052268000347139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_587
      · exact prime_fiftyFourAZ_2215464064147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3956052268000347139) ^ 1978026134000173569 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3956052268000347139) ^ 1318684089333449046 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3956052268000347139) ^ 304311712923103626 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3956052268000347139) ^ 6739441683135174 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3956052268000347139) ^ 1785654 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4552428754707023791 : Nat.Prime 4552428754707023791 := by
  apply lucas_primality 4552428754707023791 (6 : ZMod 4552428754707023791)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (50582541718966931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (50582541718966931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4552428754707023791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_50582541718966931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4552428754707023791) ^ 2276214377353511895 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552428754707023791) ^ 1517476251569007930 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552428754707023791) ^ 910485750941404758 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552428754707023791) ^ 90 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_7810572945331918127 : Nat.Prime 7810572945331918127 := by
  apply lucas_primality 7810572945331918127 (5 : ZMod 7810572945331918127)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (263, 1), (144165029076967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (263, 1), (144165029076967, 1)] : List FactorBlock).map factorBlockValue).prod) = 7810572945331918127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_103
      · exact prime_fiftyFourAZ_263
      · exact prime_fiftyFourAZ_144165029076967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7810572945331918127) ^ 3905286472665959063 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 75830805294484642 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 29697995989855202 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 7810572945331918127) ^ 54178 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_439
      · exact prime_fiftyFourAZ_853
      · exact prime_fiftyFourAZ_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_9968812463510331227 : Nat.Prime 9968812463510331227 := by
  apply lucas_primality 9968812463510331227 (2 : ZMod 9968812463510331227)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8837, 1), (61487, 1), (9173293127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8837, 1), (61487, 1), (9173293127, 1)] : List FactorBlock).map factorBlockValue).prod) = 9968812463510331227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_8837
      · exact prime_fiftyFourAZ_61487
      · exact prime_fiftyFourAZ_9173293127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9968812463510331227) ^ 4984406231755165613 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9968812463510331227) ^ 1128076548999698 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9968812463510331227) ^ 162128782726598 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9968812463510331227) ^ 1086721238 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_19737833053457806831 : Nat.Prime 19737833053457806831 := by
  apply lucas_primality 19737833053457806831 (15 : ZMod 19737833053457806831)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (151632149, 1), (1446324263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (151632149, 1), (1446324263, 1)] : List FactorBlock).map factorBlockValue).prod) = 19737833053457806831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_151632149
      · exact prime_fiftyFourAZ_1446324263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 19737833053457806831) ^ 9868916526728903415 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 6579277684485935610 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 3947566610691561366 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 130169183670 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (15 : ZMod 19737833053457806831) ^ 13646893410 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_20572881415656670829 : Nat.Prime 20572881415656670829 := by
  apply lucas_primality 20572881415656670829 (2 : ZMod 20572881415656670829)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (137, 1), (1693, 1), (67819, 1), (3593063, 1)] : List FactorBlock).map factorBlockValue).prod) = 20572881415656670829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_137
      · exact prime_fiftyFourAZ_1693
      · exact prime_fiftyFourAZ_67819
      · exact prime_fiftyFourAZ_3593063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20572881415656670829) ^ 10286440707828335414 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 2938983059379524404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 1582529339665897756 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 150167017632530444 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 12151731491823196 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 303349819603012 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20572881415656670829) ^ 5725722431156 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_32099548619639871113 : Nat.Prime 32099548619639871113 := by
  apply lucas_primality 32099548619639871113 (3 : ZMod 32099548619639871113)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (359, 1), (11176723056977671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (359, 1), (11176723056977671, 1)] : List FactorBlock).map factorBlockValue).prod) = 32099548619639871113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_359
      · exact prime_fiftyFourAZ_11176723056977671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32099548619639871113) ^ 16049774309819935556 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 32099548619639871113) ^ 89413784455821368 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 32099548619639871113) ^ 2872 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_40093901583788580553 : Nat.Prime 40093901583788580553 := by
  apply lucas_primality 40093901583788580553 (5 : ZMod 40093901583788580553)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (404191789, 1), (459237223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (404191789, 1), (459237223, 1)] : List FactorBlock).map factorBlockValue).prod) = 40093901583788580553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_404191789
      · exact prime_fiftyFourAZ_459237223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40093901583788580553) ^ 20046950791894290276 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 13364633861262860184 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 99195240168 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 40093901583788580553) ^ 87305426424 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_42695052666442357879 : Nat.Prime 42695052666442357879 := by
  apply lucas_primality 42695052666442357879 (3 : ZMod 42695052666442357879)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (87849902605848473, 1)] : List FactorBlock).map factorBlockValue).prod) = 42695052666442357879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_87849902605848473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42695052666442357879) ^ 21347526333221178939 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 14231684222147452626 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 42695052666442357879) ^ 486 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_43916097622182558197 : Nat.Prime 43916097622182558197 := by
  apply lucas_primality 43916097622182558197 (2 : ZMod 43916097622182558197)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (821, 1), (13372745926364969, 1)] : List FactorBlock).map factorBlockValue).prod) = 43916097622182558197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_821
      · exact prime_fiftyFourAZ_13372745926364969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43916097622182558197) ^ 21958048811091279098 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 53490983705459876 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43916097622182558197) ^ 3284 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_63970908826694406967 : Nat.Prime 63970908826694406967 := by
  apply lucas_primality 63970908826694406967 (3 : ZMod 63970908826694406967)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (11, 1), (13, 1), (5659, 1), (14303, 1), (11372171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (11, 1), (13, 1), (5659, 1), (14303, 1), (11372171, 1)] : List FactorBlock).map factorBlockValue).prod) = 63970908826694406967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_5659
      · exact prime_fiftyFourAZ_14303
      · exact prime_fiftyFourAZ_11372171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63970908826694406967) ^ 31985454413347203483 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 21323636275564802322 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 5815537166063127906 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 4920839140514954382 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 11304277933679874 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 4472551830154122 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63970908826694406967) ^ 5625215170146 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_75469418233448948783 : Nat.Prime 75469418233448948783 := by
  apply lucas_primality 75469418233448948783 (5 : ZMod 75469418233448948783)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26171, 1), (2503121, 1), (576021701, 1)] : List FactorBlock).map factorBlockValue).prod) = 75469418233448948783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_26171
      · exact prime_fiftyFourAZ_2503121
      · exact prime_fiftyFourAZ_576021701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75469418233448948783) ^ 37734709116724474391 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 2883704032457642 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 30150127873742 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 75469418233448948783) ^ 131018359382 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_92259445641899967061 : Nat.Prime 92259445641899967061 := by
  apply lucas_primality 92259445641899967061 (2 : ZMod 92259445641899967061)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 3), (14821679, 1), (302460083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 3), (14821679, 1), (302460083, 1)] : List FactorBlock).map factorBlockValue).prod) = 92259445641899967061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_14821679
      · exact prime_fiftyFourAZ_302460083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92259445641899967061) ^ 46129722820949983530 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 30753148547299989020 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 18451889128379993412 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 13179920805985709580 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 6224628508140 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 92259445641899967061) ^ 305030153820 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_92617653403295129287 : Nat.Prime 92617653403295129287 := by
  apply lucas_primality 92617653403295129287 (3 : ZMod 92617653403295129287)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1141573, 1), (4507311568399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1141573, 1), (4507311568399, 1)] : List FactorBlock).map factorBlockValue).prod) = 92617653403295129287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_1141573
      · exact prime_fiftyFourAZ_4507311568399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 92617653403295129287) ^ 46308826701647564643 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 92617653403295129287) ^ 30872551134431709762 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 92617653403295129287) ^ 81131608231182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 92617653403295129287) ^ 20548314 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_106788750604720147493 : Nat.Prime 106788750604720147493 := by
  apply lucas_primality 106788750604720147493 (2 : ZMod 106788750604720147493)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (33749, 1), (791051220811877, 1)] : List FactorBlock).map factorBlockValue).prod) = 106788750604720147493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_33749
      · exact prime_fiftyFourAZ_791051220811877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106788750604720147493) ^ 53394375302360073746 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 3164204883247508 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 106788750604720147493) ^ 134996 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_128630287222721314451 : Nat.Prime 128630287222721314451 := by
  apply lucas_primality 128630287222721314451 (6 : ZMod 128630287222721314451)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (563, 1), (24442633, 1), (26706613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (563, 1), (24442633, 1), (26706613, 1)] : List FactorBlock).map factorBlockValue).prod) = 128630287222721314451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_563
      · exact prime_fiftyFourAZ_24442633
      · exact prime_fiftyFourAZ_26706613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 128630287222721314451) ^ 64315143611360657225 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 128630287222721314451) ^ 25726057444544262890 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 128630287222721314451) ^ 18375755317531616350 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 128630287222721314451) ^ 228472979081210150 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 128630287222721314451) ^ 5262538091650 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (6 : ZMod 128630287222721314451) ^ 4816420832650 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_150223434544060480601 : Nat.Prime 150223434544060480601 := by
  apply lucas_primality 150223434544060480601 (3 : ZMod 150223434544060480601)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (17, 1), (421, 1), (104948605941079, 1)] : List FactorBlock).map factorBlockValue).prod) = 150223434544060480601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_421
      · exact prime_fiftyFourAZ_104948605941079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150223434544060480601) ^ 75111717272030240300 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 30044686908812096120 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 8836672620238851800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 356825260199668600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 150223434544060480601) ^ 1431400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_175768162351756354129 : Nat.Prime 175768162351756354129 := by
  apply lucas_primality 175768162351756354129 (11 : ZMod 175768162351756354129)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (167123389, 1), (3130139557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (167123389, 1), (3130139557, 1)] : List FactorBlock).map factorBlockValue).prod) = 175768162351756354129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_167123389
      · exact prime_fiftyFourAZ_3130139557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 175768162351756354129) ^ 87884081175878177064 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 58589387450585451376 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 25109737478822336304 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 1051726891152 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 175768162351756354129) ^ 56153458704 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_222399711696533019959 : Nat.Prime 222399711696533019959 := by
  apply lucas_primality 222399711696533019959 (13 : ZMod 222399711696533019959)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (56269, 1), (461233, 1), (13265149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (56269, 1), (461233, 1), (13265149, 1)] : List FactorBlock).map factorBlockValue).prod) = 222399711696533019959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_56269
      · exact prime_fiftyFourAZ_461233
      · exact prime_fiftyFourAZ_13265149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 222399711696533019959) ^ 111199855848266509979 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 222399711696533019959) ^ 13082335982149001174 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 222399711696533019959) ^ 11705247984028053682 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 222399711696533019959) ^ 3952437606791182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 222399711696533019959) ^ 482185168226326 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (13 : ZMod 222399711696533019959) ^ 16765715311342 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_199
      · exact prime_fiftyFourAZ_5449
      · exact prime_fiftyFourAZ_8089
      · exact prime_fiftyFourAZ_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_444799423393066039919 : Nat.Prime 444799423393066039919 := by
  apply lucas_primality 444799423393066039919 (11 : ZMod 444799423393066039919)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (222399711696533019959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (222399711696533019959, 1)] : List FactorBlock).map factorBlockValue).prod) = 444799423393066039919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_222399711696533019959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 444799423393066039919) ^ 222399711696533019959 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 444799423393066039919) ^ 2 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_601970919600140858567 : Nat.Prime 601970919600140858567 := by
  apply lucas_primality 601970919600140858567 (5 : ZMod 601970919600140858567)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21066299, 1), (14287533837817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21066299, 1), (14287533837817, 1)] : List FactorBlock).map factorBlockValue).prod) = 601970919600140858567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_21066299
      · exact prime_fiftyFourAZ_14287533837817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 601970919600140858567) ^ 300985459800070429283 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 601970919600140858567) ^ 28575067675634 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 601970919600140858567) ^ 42132598 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_708367157122331656487 : Nat.Prime 708367157122331656487 := by
  apply lucas_primality 708367157122331656487 (5 : ZMod 708367157122331656487)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (143881, 1), (2461642458428603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (143881, 1), (2461642458428603, 1)] : List FactorBlock).map factorBlockValue).prod) = 708367157122331656487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_143881
      · exact prime_fiftyFourAZ_2461642458428603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 708367157122331656487) ^ 354183578561165828243 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 708367157122331656487) ^ 4923284916857206 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 708367157122331656487) ^ 287762 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_815485783052806974419 : Nat.Prime 815485783052806974419 := by
  apply lucas_primality 815485783052806974419 (2 : ZMod 815485783052806974419)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4091, 1), (99668269744904299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4091, 1), (99668269744904299, 1)] : List FactorBlock).map factorBlockValue).prod) = 815485783052806974419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_4091
      · exact prime_fiftyFourAZ_99668269744904299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 815485783052806974419) ^ 407742891526403487209 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 815485783052806974419) ^ 199336539489808598 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 815485783052806974419) ^ 8182 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1299235385747572180099 : Nat.Prime 1299235385747572180099 := by
  apply lucas_primality 1299235385747572180099 (2 : ZMod 1299235385747572180099)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11120643179, 1), (19471826177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299235385747572180099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11120643179
      · exact prime_fiftyFourAZ_19471826177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299235385747572180099) ^ 649617692873786090049 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 433078461915857393366 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 116830957062 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299235385747572180099) ^ 66723859074 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1813852357585221913373 : Nat.Prime 1813852357585221913373 := by
  apply lucas_primality 1813852357585221913373 (2 : ZMod 1813852357585221913373)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (327337, 1), (197901371804377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (327337, 1), (197901371804377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1813852357585221913373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_327337
      · exact prime_fiftyFourAZ_197901371804377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1813852357585221913373) ^ 906926178792610956686 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 259121765369317416196 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 5541238410522556 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1813852357585221913373) ^ 9165436 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_107
      · exact prime_fiftyFourAZ_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2795510963517306639443 : Nat.Prime 2795510963517306639443 := by
  apply lucas_primality 2795510963517306639443 (2 : ZMod 2795510963517306639443)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (253853, 1), (15003163417171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (253853, 1), (15003163417171, 1)] : List FactorBlock).map factorBlockValue).prod) = 2795510963517306639443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_367
      · exact prime_fiftyFourAZ_253853
      · exact prime_fiftyFourAZ_15003163417171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2795510963517306639443) ^ 1397755481758653319721 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2795510963517306639443) ^ 7617196085878219726 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2795510963517306639443) ^ 11012321948203514 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2795510963517306639443) ^ 186328102 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2820005742344536930967 : Nat.Prime 2820005742344536930967 := by
  apply lucas_primality 2820005742344536930967 (5 : ZMod 2820005742344536930967)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1289, 1), (1093873445440084147, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820005742344536930967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_1289
      · exact prime_fiftyFourAZ_1093873445440084147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2820005742344536930967) ^ 1410002871172268465483 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2187746890880168294 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2820005742344536930967) ^ 2578 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_7178534534772569414123 : Nat.Prime 7178534534772569414123 := by
  apply lucas_primality 7178534534772569414123 (2 : ZMod 7178534534772569414123)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (246391, 1), (14702459, 1), (990811369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (246391, 1), (14702459, 1), (990811369, 1)] : List FactorBlock).map factorBlockValue).prod) = 7178534534772569414123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_246391
      · exact prime_fiftyFourAZ_14702459
      · exact prime_fiftyFourAZ_990811369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7178534534772569414123) ^ 3589267267386284707061 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 29134727058912742 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 488254008038558 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7178534534772569414123) ^ 7245107150938 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_12829801099686321293111 : Nat.Prime 12829801099686321293111 := by
  apply lucas_primality 12829801099686321293111 (14 : ZMod 12829801099686321293111)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (75469418233448948783, 1)] : List FactorBlock).map factorBlockValue).prod) = 12829801099686321293111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_75469418233448948783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 12829801099686321293111) ^ 6414900549843160646555 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 2565960219937264258622 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 754694182334489487830 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (14 : ZMod 12829801099686321293111) ^ 170 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_34856564291144180525293 : Nat.Prime 34856564291144180525293 := by
  apply lucas_primality 34856564291144180525293 (5 : ZMod 34856564291144180525293)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (37, 1), (2273, 1), (3139854234712031, 1)] : List FactorBlock).map factorBlockValue).prod) = 34856564291144180525293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_2273
      · exact prime_fiftyFourAZ_3139854234712031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34856564291144180525293) ^ 17428282145572090262646 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11618854763714726841764 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 3168778571922198229572 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 942069305166058933116 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 15335048082333559404 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 34856564291144180525293) ^ 11101332 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_56669372569786532518961 : Nat.Prime 56669372569786532518961 := by
  apply lucas_primality 56669372569786532518961 (3 : ZMod 56669372569786532518961)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (708367157122331656487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (708367157122331656487, 1)] : List FactorBlock).map factorBlockValue).prod) = 56669372569786532518961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_708367157122331656487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 56669372569786532518961) ^ 28334686284893266259480 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 56669372569786532518961) ^ 11333874513957306503792 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 56669372569786532518961) ^ 80 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_61781265172855594114757 : Nat.Prime 61781265172855594114757 := by
  apply lucas_primality 61781265172855594114757 (2 : ZMod 61781265172855594114757)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1153, 1), (43499, 1), (301649, 1), (145843909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1153, 1), (43499, 1), (301649, 1), (145843909, 1)] : List FactorBlock).map factorBlockValue).prod) = 61781265172855594114757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_1153
      · exact prime_fiftyFourAZ_43499
      · exact prime_fiftyFourAZ_301649
      · exact prime_fiftyFourAZ_145843909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61781265172855594114757) ^ 30890632586427797057378 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61781265172855594114757) ^ 8825895024693656302108 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61781265172855594114757) ^ 53583057391895571652 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61781265172855594114757) ^ 1420291619872999244 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61781265172855594114757) ^ 204811768555027844 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61781265172855594114757) ^ 423612241309684 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_71241401185919644928609 : Nat.Prime 71241401185919644928609 := by
  apply lucas_primality 71241401185919644928609 (3 : ZMod 71241401185919644928609)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (21580023643, 1), (103164566633, 1)] : List FactorBlock).map factorBlockValue).prod) = 71241401185919644928609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_21580023643
      · exact prime_fiftyFourAZ_103164566633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71241401185919644928609) ^ 35620700592959822464304 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 3301266132256 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 71241401185919644928609) ^ 690560756576 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_93596301651291302272987 : Nat.Prime 93596301651291302272987 := by
  apply lucas_primality 93596301651291302272987 (2 : ZMod 93596301651291302272987)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3616901, 1), (5004841, 1), (287249497, 1)] : List FactorBlock).map factorBlockValue).prod) = 93596301651291302272987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_3616901
      · exact prime_fiftyFourAZ_5004841
      · exact prime_fiftyFourAZ_287249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93596301651291302272987) ^ 46798150825645651136493 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 31198767217097100757662 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 25877485076669586 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 18701153873078346 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93596301651291302272987) ^ 325836259519338 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_140071023992734314888157 : Nat.Prime 140071023992734314888157 := by
  apply lucas_primality 140071023992734314888157 (2 : ZMod 140071023992734314888157)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (4231, 1), (64574753, 1), (6103279213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (4231, 1), (64574753, 1), (6103279213, 1)] : List FactorBlock).map factorBlockValue).prod) = 140071023992734314888157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_4231
      · exact prime_fiftyFourAZ_64574753
      · exact prime_fiftyFourAZ_6103279213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140071023992734314888157) ^ 70035511996367157444078 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 46690341330911438296052 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 20010146284676330698308 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 33105890804238788676 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 2169129845417052 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 140071023992734314888157) ^ 22950125515212 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_183636732118969333034993 : Nat.Prime 183636732118969333034993 := by
  apply lucas_primality 183636732118969333034993 (5 : ZMod 183636732118969333034993)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (113, 1), (110261, 1), (131595537606037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (113, 1), (110261, 1), (131595537606037, 1)] : List FactorBlock).map factorBlockValue).prod) = 183636732118969333034993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_113
      · exact prime_fiftyFourAZ_110261
      · exact prime_fiftyFourAZ_131595537606037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 183636732118969333034993) ^ 91818366059484666517496 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 26233818874138476147856 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1625103824061675513584 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1665473123942004272 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 183636732118969333034993) ^ 1395463216 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_300098768163432966586193 : Nat.Prime 300098768163432966586193 := by
  apply lucas_primality 300098768163432966586193 (3 : ZMod 300098768163432966586193)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (815485783052806974419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (815485783052806974419, 1)] : List FactorBlock).map factorBlockValue).prod) = 300098768163432966586193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_815485783052806974419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 300098768163432966586193) ^ 150049384081716483293096 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 300098768163432966586193) ^ 13047772528844911590704 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 300098768163432966586193) ^ 368 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_301563079481128940958473 : Nat.Prime 301563079481128940958473 := by
  apply lucas_primality 301563079481128940958473 (5 : ZMod 301563079481128940958473)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (37, 1), (92617653403295129287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (37, 1), (92617653403295129287, 1)] : List FactorBlock).map factorBlockValue).prod) = 301563079481128940958473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_92617653403295129287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 301563079481128940958473) ^ 150781539740564470479236 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 301563079481128940958473) ^ 27414825407375358268952 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 301563079481128940958473) ^ 8150353499489971377256 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 301563079481128940958473) ^ 3256 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_408403242931592497828927 : Nat.Prime 408403242931592497828927 := by
  apply lucas_primality 408403242931592497828927 (3 : ZMod 408403242931592497828927)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (169787494937, 1), (400896468733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (169787494937, 1), (400896468733, 1)] : List FactorBlock).map factorBlockValue).prod) = 408403242931592497828927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_169787494937
      · exact prime_fiftyFourAZ_400896468733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 408403242931592497828927) ^ 204201621465796248914463 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 136134414310530832609642 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 2405378812398 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 408403242931592497828927) ^ 1018724969622 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_549867893213491257444671 : Nat.Prime 549867893213491257444671 := by
  apply lucas_primality 549867893213491257444671 (11 : ZMod 549867893213491257444671)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2221, 1), (281055143, 1), (88088307689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2221, 1), (281055143, 1), (88088307689, 1)] : List FactorBlock).map factorBlockValue).prod) = 549867893213491257444671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_2221
      · exact prime_fiftyFourAZ_281055143
      · exact prime_fiftyFourAZ_88088307689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 549867893213491257444671) ^ 274933946606745628722335 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 549867893213491257444671) ^ 109973578642698251488934 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 549867893213491257444671) ^ 247576719141598945270 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 549867893213491257444671) ^ 1956441313772690 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (11 : ZMod 549867893213491257444671) ^ 6242234726030 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1532168852393981051301083 : Nat.Prime 1532168852393981051301083 := by
  apply lucas_primality 1532168852393981051301083 (2 : ZMod 1532168852393981051301083)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (2281, 1), (7810572945331918127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (2281, 1), (7810572945331918127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1532168852393981051301083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_2281
      · exact prime_fiftyFourAZ_7810572945331918127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1532168852393981051301083) ^ 766084426196990525650541 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 35631833776604210495374 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 671709273298544958922 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1532168852393981051301083) ^ 196166 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_8839990548539518477653493 : Nat.Prime 8839990548539518477653493 := by
  apply lucas_primality 8839990548539518477653493 (5 : ZMod 8839990548539518477653493)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (337, 1), (3656251, 1), (45989776525361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (337, 1), (3656251, 1), (45989776525361, 1)] : List FactorBlock).map factorBlockValue).prod) = 8839990548539518477653493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_337
      · exact prime_fiftyFourAZ_3656251
      · exact prime_fiftyFourAZ_45989776525361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8839990548539518477653493) ^ 4419995274269759238826746 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 2946663516179839492551164 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 679999272964578344434884 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 26231425960057918331316 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 2417774531491278492 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8839990548539518477653493) ^ 192216427572 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_14940887372233185688184771 : Nat.Prime 14940887372233185688184771 := by
  apply lucas_primality 14940887372233185688184771 (2 : ZMod 14940887372233185688184771)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26075531717, 1), (57298495518281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26075531717, 1), (57298495518281, 1)] : List FactorBlock).map factorBlockValue).prod) = 14940887372233185688184771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_26075531717
      · exact prime_fiftyFourAZ_57298495518281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14940887372233185688184771) ^ 7470443686116592844092385 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940887372233185688184771) ^ 2988177474446637137636954 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940887372233185688184771) ^ 572984955182810 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940887372233185688184771) ^ 260755317170 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_18905067142893811799115643 : Nat.Prime 18905067142893811799115643 := by
  apply lucas_primality 18905067142893811799115643 (2 : ZMod 18905067142893811799115643)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (61781265172855594114757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (61781265172855594114757, 1)] : List FactorBlock).map factorBlockValue).prod) = 18905067142893811799115643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_61781265172855594114757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18905067142893811799115643) ^ 9452533571446905899557821 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 18905067142893811799115643) ^ 6301689047631270599705214 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 18905067142893811799115643) ^ 1112062773111400694065626 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 18905067142893811799115643) ^ 306 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_36315365040701025281918957 : Nat.Prime 36315365040701025281918957 := by
  apply lucas_primality 36315365040701025281918957 (2 : ZMod 36315365040701025281918957)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (93596301651291302272987, 1)] : List FactorBlock).map factorBlockValue).prod) = 36315365040701025281918957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_97
      · exact prime_fiftyFourAZ_93596301651291302272987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36315365040701025281918957) ^ 18157682520350512640959478 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 374385206605165209091948 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 36315365040701025281918957) ^ 388 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_38459284181658073762417787 : Nat.Prime 38459284181658073762417787 := by
  apply lucas_primality 38459284181658073762417787 (2 : ZMod 38459284181658073762417787)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (4382406037, 1), (107022411157729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (4382406037, 1), (107022411157729, 1)] : List FactorBlock).map factorBlockValue).prod) = 38459284181658073762417787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_4382406037
      · exact prime_fiftyFourAZ_107022411157729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38459284181658073762417787) ^ 19229642090829036881208893 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 938031321503855457619946 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 8775837714933778 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38459284181658073762417787) ^ 359357295034 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_65952904691686366162823891 : Nat.Prime 65952904691686366162823891 := by
  apply lucas_primality 65952904691686366162823891 (2 : ZMod 65952904691686366162823891)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (269, 1), (1966233961, 1), (12469425776321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (269, 1), (1966233961, 1), (12469425776321, 1)] : List FactorBlock).map factorBlockValue).prod) = 65952904691686366162823891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_269
      · exact prime_fiftyFourAZ_1966233961
      · exact prime_fiftyFourAZ_12469425776321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65952904691686366162823891) ^ 32976452345843183081411945 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 13190580938337273232564778 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 245178084355711398374810 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 33542755338303490 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 65952904691686366162823891) ^ 5289169355090 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_70311026147084143662569963 : Nat.Prime 70311026147084143662569963 := by
  apply lucas_primality 70311026147084143662569963 (2 : ZMod 70311026147084143662569963)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (579178573, 1), (60698918627885897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (579178573, 1), (60698918627885897, 1)] : List FactorBlock).map factorBlockValue).prod) = 70311026147084143662569963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_579178573
      · exact prime_fiftyFourAZ_60698918627885897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70311026147084143662569963) ^ 35155513073542071831284981 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 70311026147084143662569963) ^ 121397837255771794 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 70311026147084143662569963) ^ 1158357146 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_278787824198918787972111469 : Nat.Prime 278787824198918787972111469 := by
  apply lucas_primality 278787824198918787972111469 (2 : ZMod 278787824198918787972111469)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (2749, 1), (444799423393066039919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (2749, 1), (444799423393066039919, 1)] : List FactorBlock).map factorBlockValue).prod) = 278787824198918787972111469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_2749
      · exact prime_fiftyFourAZ_444799423393066039919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 278787824198918787972111469) ^ 139393912099459393986055734 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278787824198918787972111469) ^ 92929274732972929324037156 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278787824198918787972111469) ^ 14673043378890462524847972 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278787824198918787972111469) ^ 101414268533619057101532 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 278787824198918787972111469) ^ 626772 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_686477545608090348877564801 : Nat.Prime 686477545608090348877564801 := by
  apply lucas_primality 686477545608090348877564801 (83 : ZMod 686477545608090348877564801)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 5), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 686477545608090348877564801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 686477545608090348877564801) ^ 343238772804045174438782400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 228825848536030116292521600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 137295509121618069775512960 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 98068220801155764125366400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 62407049600735486261596800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 52805965046776180682889600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 40381032094593549933974400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 36130397137267913098819200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 29846849809047406472937600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 23671639503727253409571200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 18553447178597036456150400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 16743354770929032899452800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 15964594083909077880873600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 14605905225704049976118400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 12952406520907365073161600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11635212637425260150467200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 686477545608090348877564801) ^ 11253730255870333588156800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_808131794196865853741943373 : Nat.Prime 808131794196865853741943373 := by
  apply lucas_primality 808131794196865853741943373 (2 : ZMod 808131794196865853741943373)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (189067, 1), (2202311, 1), (161735950924213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (189067, 1), (2202311, 1), (161735950924213, 1)] : List FactorBlock).map factorBlockValue).prod) = 808131794196865853741943373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_189067
      · exact prime_fiftyFourAZ_2202311
      · exact prime_fiftyFourAZ_161735950924213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 808131794196865853741943373) ^ 404065897098432926870971686 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 808131794196865853741943373) ^ 269377264732288617913981124 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 808131794196865853741943373) ^ 4274314365790253474916 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 808131794196865853741943373) ^ 366947172400658151252 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (2 : ZMod 808131794196865853741943373) ^ 4996612006044 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_829122230409771460332643201 : Nat.Prime 829122230409771460332643201 := by
  apply lucas_primality 829122230409771460332643201 (73 : ZMod 829122230409771460332643201)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 6), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 6), (5, 2), (7, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 829122230409771460332643201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 829122230409771460332643201) ^ 414561115204885730166321600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 276374076803257153444214400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 165824446081954292066528640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 118446032915681637190377600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 63778633108443958487126400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 48771895906457144725449600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 43638012126830076859612800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 36048792626511802623158400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 28590421738267981390780800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 26745878400315208397827200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 22408708929993823252233600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 20222493424628572203235200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 19281912335110964193782400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 17640898519356839581545600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 15643815668108895477974400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 14052919159487651870044800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (73 : ZMod 829122230409771460332643201) ^ 13592167711635597710371200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_1100731236923317283545060801 : Nat.Prime 1100731236923317283545060801 := by
  apply lucas_primality 1100731236923317283545060801 (71 : ZMod 1100731236923317283545060801)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100731236923317283545060801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 1100731236923317283545060801) ^ 550365618461658641772530400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 366910412307772427848353600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 220146247384663456709012160 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 157247319560473897649294400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 100066476083937934867732800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 84671633609485944888081600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 64748896289606899032062400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 57933222995964067555003200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 47857879866231186241089600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 35507459255590880114356800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 29749492889819386041758400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 26847103339593104476708800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 25598400858681797291745600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 23419813551559942203086400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 20768513904213533651793600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 18656461642768089551611200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (71 : ZMod 1100731236923317283545060801) ^ 18044774375792086615492800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_2775757032241408801983196801 : Nat.Prime 2775757032241408801983196801 := by
  apply lucas_primality 2775757032241408801983196801 (67 : ZMod 2775757032241408801983196801)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2775757032241408801983196801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 2775757032241408801983196801) ^ 1387878516120704400991598400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 925252344080469600661065600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 555151406448281760396639360 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 396536718891629828854742400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 252341548385582618362108800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 213519771710877600152553600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 163279825425965223646070400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 146092475381126779051747200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 95715759732462372482179200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 89540549427142219418812800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 75020460330848886540086400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 67701391030278263463004800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 64552489121893227953097600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 59058660260455506425174400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 52372774193234128339305600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 47046729360023877999715200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 2775757032241408801983196801) ^ 45504213643301783639068800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_3990150733847025152850845401 : Nat.Prime 3990150733847025152850845401 := by
  apply lucas_primality 3990150733847025152850845401 (67 : ZMod 3990150733847025152850845401)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3990150733847025152850845401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 3990150733847025152850845401) ^ 1995075366923512576425422700 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 1330050244615675050950281800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 798030146769405030570169080 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 570021533406717878978692200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 362740975804275013895531400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 306934671834386550219295800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 234714749049825008991226200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 210007933360369744886886600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 173484814515088050123949800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 137591404615414660443132600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 128714539801516940414543400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 107841911725595274401374200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 97320749606025003728069400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 92794203112721515182577800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 84896824124404790486188200 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 75285862902774059487751800 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 67629673455034324624590600 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (67 : ZMod 3990150733847025152850845401) ^ 65412307112246313981161400 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_4256160782770160163040901761 : Nat.Prime 4256160782770160163040901761 := by
  apply lucas_primality 4256160782770160163040901761 (83 : ZMod 4256160782770160163040901761)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 5), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4256160782770160163040901761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_3
      · exact prime_fiftyFourAZ_5
      · exact prime_fiftyFourAZ_7
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_13
      · exact prime_fiftyFourAZ_17
      · exact prime_fiftyFourAZ_19
      · exact prime_fiftyFourAZ_23
      · exact prime_fiftyFourAZ_29
      · exact prime_fiftyFourAZ_31
      · exact prime_fiftyFourAZ_37
      · exact prime_fiftyFourAZ_41
      · exact prime_fiftyFourAZ_43
      · exact prime_fiftyFourAZ_47
      · exact prime_fiftyFourAZ_53
      · exact prime_fiftyFourAZ_59
      · exact prime_fiftyFourAZ_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (83 : ZMod 4256160782770160163040901761) ^ 2128080391385080081520450880 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 1418720260923386721013633920 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 851232156554032032608180352 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 608022968967165737577271680 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 386923707524560014821900160 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 327396983290012320233915520 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 250362398986480009590641280 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 224008462251061061212679040 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 185050468816093920132213120 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 146764164923108971139341440 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 137295509121618069775512960 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 115031372507301626028132480 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 103808799579760003976607360 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 98980483320236282861416320 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 90556612399365109851934080 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 80304920429625663453601920 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 72138318352036612932896640 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (83 : ZMod 4256160782770160163040901761) ^ 69773127586396068246572160 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem prime_fiftyFourAZ_63842411741552402445613526489 : Nat.Prime 63842411741552402445613526489 := by
  apply lucas_primality 63842411741552402445613526489 (3 : ZMod 63842411741552402445613526489)
  · rw [← fiftyFourAZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (65952904691686366162823891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (65952904691686366162823891, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftyFourAZ_2
      · exact prime_fiftyFourAZ_11
      · exact prime_fiftyFourAZ_65952904691686366162823891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 63842411741552402445613526489) ^ 31921205870776201222806763244 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63842411741552402445613526489) ^ 5803855612868400222328502408 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide
    · change (3 : ZMod 63842411741552402445613526489) ^ 968 ≠ 1
      rw [← fiftyFourAZFastPow_eq_pow]
      decide

private theorem phi_fiftyFourAZ_63842411741552402445613526400 : Nat.totient 63842411741552402445613526400 = 8400853896805474526822400000 := by
  rw [← show ((([(2, 7), (3, 6), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_7, prime_fiftyFourAZ_11, prime_fiftyFourAZ_13, prime_fiftyFourAZ_17, prime_fiftyFourAZ_19, prime_fiftyFourAZ_23, prime_fiftyFourAZ_29, prime_fiftyFourAZ_31, prime_fiftyFourAZ_37, prime_fiftyFourAZ_41, prime_fiftyFourAZ_43, prime_fiftyFourAZ_47, prime_fiftyFourAZ_53, prime_fiftyFourAZ_59, prime_fiftyFourAZ_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526401 : Nat.totient 63842411741552402445613526401 = 63563623917353483657641414704 := by
  rw [← show ((([(229, 1), (278787824198918787972111469, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_229, prime_fiftyFourAZ_278787824198918787972111469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526402 : Nat.totient 63842411741552402445613526402 = 31921065799752208488491647152 := by
  rw [← show ((([(2, 1), (227893, 1), (140071023992734314888157, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_227893, prime_fiftyFourAZ_140071023992734314888157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526403 : Nat.totient 63842411741552402445613526403 = 42558909776595463918587787776 := by
  rw [← show ((([(3, 1), (26417, 1), (39157, 1), (20572881415656670829, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_26417, prime_fiftyFourAZ_39157, prime_fiftyFourAZ_20572881415656670829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526404 : Nat.totient 63842411741552402445613526404 = 31780583818482032935481622824 := by
  rw [← show ((([(2, 2), (227, 1), (70311026147084143662569963, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_227, prime_fiftyFourAZ_70311026147084143662569963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526405 : Nat.totient 63842411741552402445613526405 = 50993890686131610546276480000 := by
  rw [← show ((([(5, 1), (751, 1), (4241, 1), (12910379, 1), (310521788772829, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_751, prime_fiftyFourAZ_4241, prime_fiftyFourAZ_12910379, prime_fiftyFourAZ_310521788772829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526406 : Nat.totient 63842411741552402445613526406 = 21208173183769398764640670304 := by
  rw [← show ((([(2, 1), (3, 1), (293, 1), (36315365040701025281918957, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_293, prime_fiftyFourAZ_36315365040701025281918957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526407 : Nat.totient 63842411741552402445613526407 = 54687706205805065791278786528 := by
  rw [← show ((([(7, 1), (1597, 1), (572879, 1), (9968812463510331227, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_7, prime_fiftyFourAZ_1597, prime_fiftyFourAZ_572879, prime_fiftyFourAZ_9968812463510331227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526408 : Nat.totient 63842411741552402445613526408 = 31920471323847725345474449408 := by
  rw [← show ((([(2, 3), (43457, 1), (183636732118969333034993, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_43457, prime_fiftyFourAZ_183636732118969333034993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526409 : Nat.totient 63842411741552402445613526409 = 42561240608877117829114754880 := by
  rw [← show ((([(3, 2), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_115903, prime_fiftyFourAZ_32244294937, prime_fiftyFourAZ_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526410 : Nat.totient 63842411741552402445613526410 = 25536964327583178410368747200 := by
  rw [← show ((([(2, 1), (5, 1), (69198781, 1), (92259445641899967061, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_69198781, prime_fiftyFourAZ_92259445641899967061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526411 : Nat.totient 63842411741552402445613526411 = 57849505457255064105293864520 := by
  rw [← show ((([(11, 1), (307, 1), (18905067142893811799115643, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_11, prime_fiftyFourAZ_307, prime_fiftyFourAZ_18905067142893811799115643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526412 : Nat.totient 63842411741552402445613526412 = 21272809460526560612669875200 := by
  rw [← show ((([(2, 2), (3, 1), (2663, 1), (9063547, 1), (26126021, 1), (8436948721, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_2663, prime_fiftyFourAZ_9063547, prime_fiftyFourAZ_26126021, prime_fiftyFourAZ_8436948721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526413 : Nat.totient 63842411741552402445613526413 = 58931456992193541771285427200 := by
  rw [← show ((([(13, 1), (6857614732721, 1), (716131620214481, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_13, prime_fiftyFourAZ_6857614732721, prime_fiftyFourAZ_716131620214481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526414 : Nat.totient 63842411741552402445613526414 = 27105323008971450352600001088 := by
  rw [← show ((([(2, 1), (7, 1), (107, 1), (216104610427, 1), (197212046147609, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_7, prime_fiftyFourAZ_107, prime_fiftyFourAZ_216104610427, prime_fiftyFourAZ_197212046147609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526415 : Nat.totient 63842411741552402445613526415 = 34049286262161281304327214080 := by
  rw [← show ((([(3, 1), (5, 1), (4256160782770160163040901761, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_4256160782770160163040901761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526416 : Nat.totient 63842411741552402445613526416 = 31921205870776201222806763200 := by
  rw [← show ((([(2, 4), (3990150733847025152850845401, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3990150733847025152850845401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526417 : Nat.totient 63842411741552402445613526417 = 59864347681749596304156499200 := by
  rw [← show ((([(17, 1), (271, 1), (67079, 1), (4805179, 1), (42992720020091, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_17, prime_fiftyFourAZ_271, prime_fiftyFourAZ_67079, prime_fiftyFourAZ_4805179, prime_fiftyFourAZ_42992720020091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526418 : Nat.totient 63842411741552402445613526418 = 21280803913151441936032356600 := by
  rw [← show ((([(2, 1), (3, 2), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_30429025931, prime_fiftyFourAZ_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526419 : Nat.totient 63842411741552402445613526419 = 60482284807754809606706044416 := by
  rw [← show ((([(19, 1), (1911424697713, 1), (1757917504040977, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_19, prime_fiftyFourAZ_1911424697713, prime_fiftyFourAZ_1757917504040977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526420 : Nat.totient 63842411741552402445613526420 = 25229290423167696388146067616 := by
  rw [← show ((([(2, 2), (5, 1), (83, 1), (38459284181658073762417787, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_83, prime_fiftyFourAZ_38459284181658073762417787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526421 : Nat.totient 63842411741552402445613526421 = 36470504732797065379846899456 := by
  rw [← show ((([(3, 1), (7, 1), (4177, 1), (17047, 1), (42695052666442357879, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_7, prime_fiftyFourAZ_4177, prime_fiftyFourAZ_17047, prime_fiftyFourAZ_42695052666442357879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526422 : Nat.totient 63842411741552402445613526422 = 28977861734208663219192816000 := by
  rw [← show ((([(2, 1), (11, 1), (701, 1), (1686677, 1), (13313779, 1), (184346679547, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_11, prime_fiftyFourAZ_701, prime_fiftyFourAZ_1686677, prime_fiftyFourAZ_13313779, prime_fiftyFourAZ_184346679547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526423 : Nat.totient 63842411741552402445613526423 = 61066654709310993643630329600 := by
  rw [← show ((([(23, 1), (2775757032241408801983196801, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_23, prime_fiftyFourAZ_2775757032241408801983196801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526424 : Nat.totient 63842411741552402445613526424 = 21272918339361761714570256384 := by
  rw [← show ((([(2, 3), (3, 1), (3137, 1), (19309, 1), (43916097622182558197, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_3137, prime_fiftyFourAZ_19309, prime_fiftyFourAZ_43916097622182558197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526425 : Nat.totient 63842411741552402445613526425 = 50937788009318629123131725760 := by
  rw [← show ((([(5, 2), (463, 1), (1973, 1), (2795510963517306639443, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_463, prime_fiftyFourAZ_1973, prime_fiftyFourAZ_2795510963517306639443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526426 : Nat.totient 63842411741552402445613526426 = 29243798587348207586541964800 := by
  rw [← show ((([(2, 1), (13, 1), (233, 1), (311, 1), (25903, 1), (614266579, 1), (2129671771, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_13, prime_fiftyFourAZ_233, prime_fiftyFourAZ_311, prime_fiftyFourAZ_25903, prime_fiftyFourAZ_614266579, prime_fiftyFourAZ_2129671771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526427 : Nat.totient 63842411741552402445613526427 = 42561405339474935178136935936 := by
  rw [← show ((([(3, 3), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_210193, prime_fiftyFourAZ_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526428 : Nat.totient 63842411741552402445613526428 = 27361033601890680524003494464 := by
  rw [← show ((([(2, 2), (7, 1), (16767625597, 1), (135981455480185333, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_7, prime_fiftyFourAZ_16767625597, prime_fiftyFourAZ_135981455480185333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526429 : Nat.totient 63842411741552402445613526429 = 61608754135856218514807875200 := by
  rw [← show ((([(29, 1), (2777, 1), (6163, 1), (128630287222721314451, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_29, prime_fiftyFourAZ_2777, prime_fiftyFourAZ_6163, prime_fiftyFourAZ_128630287222721314451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526430 : Nat.totient 63842411741552402445613526430 = 17019022488969288677097600000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3181, 1), (73571, 1), (455881, 1), (19946477413151, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_3181, prime_fiftyFourAZ_73571, prime_fiftyFourAZ_455881, prime_fiftyFourAZ_19946477413151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526431 : Nat.totient 63842411741552402445613526431 = 61782146962123193439781708800 := by
  rw [← show ((([(31, 1), (91009, 1), (403079, 1), (56140086323316791, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_31, prime_fiftyFourAZ_91009, prime_fiftyFourAZ_403079, prime_fiftyFourAZ_56140086323316791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526432 : Nat.totient 63842411741552402445613526432 = 31875676135068684313788825600 := by
  rw [← show ((([(2, 5), (1559, 1), (2521, 1), (2591, 1), (342553, 1), (571933002133, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_1559, prime_fiftyFourAZ_2521, prime_fiftyFourAZ_2591, prime_fiftyFourAZ_342553, prime_fiftyFourAZ_571933002133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526433 : Nat.totient 63842411741552402445613526433 = 38692114156434007755761138000 := by
  rw [← show ((([(3, 1), (11, 1), (150791, 1), (12829801099686321293111, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_11, prime_fiftyFourAZ_150791, prime_fiftyFourAZ_12829801099686321293111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526434 : Nat.totient 63842411741552402445613526434 = 30038686298086986223411474432 := by
  rw [← show ((([(2, 1), (17, 1), (6257, 1), (300098768163432966586193, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_17, prime_fiftyFourAZ_6257, prime_fiftyFourAZ_300098768163432966586193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526435 : Nat.totient 63842411741552402445613526435 = 43181421522427331533209600000 := by
  rw [← show ((([(5, 1), (7, 1), (101, 1), (641, 1), (881, 1), (1039, 1), (9719, 1), (3167005364581, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_7, prime_fiftyFourAZ_101, prime_fiftyFourAZ_641, prime_fiftyFourAZ_881, prime_fiftyFourAZ_1039, prime_fiftyFourAZ_9719, prime_fiftyFourAZ_3167005364581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526436 : Nat.totient 63842411741552402445613526436 = 21277989704366903307463050240 := by
  rw [← show ((([(2, 2), (3, 2), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_8233, prime_fiftyFourAZ_93811, prime_fiftyFourAZ_8274073, prime_fiftyFourAZ_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526437 : Nat.totient 63842411741552402445613526437 = 62116941115634779124180299152 := by
  rw [← show ((([(37, 1), (1621509367, 1), (1064113857573247303, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_37, prime_fiftyFourAZ_1621509367, prime_fiftyFourAZ_1064113857573247303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526438 : Nat.totient 63842411741552402445613526438 = 30241142403655625167764174336 := by
  rw [← show ((([(2, 1), (19, 1), (127269069457, 1), (13200878061346993, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_19, prime_fiftyFourAZ_127269069457, prime_fiftyFourAZ_13200878061346993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526439 : Nat.totient 63842411741552402445613526439 = 39287634389439049370356800000 := by
  rw [← show ((([(3, 1), (13, 1), (10897001, 1), (150223434544060480601, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_13, prime_fiftyFourAZ_10897001, prime_fiftyFourAZ_150223434544060480601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526440 : Nat.totient 63842411741552402445613526440 = 25536963673086419750735702592 := by
  rw [← show ((([(2, 3), (5, 1), (24949783, 1), (63970908826694406967, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_24949783, prime_fiftyFourAZ_63970908826694406967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526441 : Nat.totient 63842411741552402445613526441 = 62119435711176684379804446720 := by
  rw [← show ((([(41, 1), (419, 1), (3617, 1), (4865743, 1), (211161009607909, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_41, prime_fiftyFourAZ_419, prime_fiftyFourAZ_3617, prime_fiftyFourAZ_4865743, prime_fiftyFourAZ_211161009607909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526442 : Nat.totient 63842411741552402445613526442 = 17966940458166031206156150528 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (67, 1), (12583, 1), (277259, 1), (2674733, 1), (2431279603, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_7, prime_fiftyFourAZ_67, prime_fiftyFourAZ_12583, prime_fiftyFourAZ_277259, prime_fiftyFourAZ_2674733, prime_fiftyFourAZ_2431279603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526443 : Nat.totient 63842411741552402445613526443 = 61894436536661993765452224000 := by
  rw [← show ((([(43, 1), (167, 1), (691, 1), (372401, 1), (34548999256651933, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_43, prime_fiftyFourAZ_167, prime_fiftyFourAZ_691, prime_fiftyFourAZ_372401, prime_fiftyFourAZ_34548999256651933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526444 : Nat.totient 63842411741552402445613526444 = 28988634687294121490616471440 := by
  rw [← show ((([(2, 2), (11, 1), (947, 1), (1532168852393981051301083, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_11, prime_fiftyFourAZ_947, prime_fiftyFourAZ_1532168852393981051301083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526445 : Nat.totient 63842411741552402445613526445 = 34016583479430296035966205952 := by
  rw [← show ((([(3, 2), (5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_1049, prime_fiftyFourAZ_139537, prime_fiftyFourAZ_175593973, prime_fiftyFourAZ_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526446 : Nat.totient 63842411741552402445613526446 = 30338847562587627415306784544 := by
  rw [← show ((([(2, 1), (23, 1), (157, 1), (8839990548539518477653493, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_23, prime_fiftyFourAZ_157, prime_fiftyFourAZ_8839990548539518477653493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526447 : Nat.totient 63842411741552402445613526447 = 61626122765471252243566998720 := by
  rw [← show ((([(47, 1), (73, 1), (30911, 1), (601970919600140858567, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_47, prime_fiftyFourAZ_73, prime_fiftyFourAZ_30911, prime_fiftyFourAZ_601970919600140858567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526448 : Nat.totient 63842411741552402445613526448 = 21255709062173240278465873920 := by
  rw [← show ((([(2, 4), (3, 1), (919, 1), (11257, 1), (425291, 1), (302303849620517, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_919, prime_fiftyFourAZ_11257, prime_fiftyFourAZ_425291, prime_fiftyFourAZ_302303849620517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526449 : Nat.totient 63842411741552402445613526449 = 54712277055835676500671211680 := by
  rw [← show ((([(7, 2), (5783, 1), (167071, 1), (970780183, 1), (1389114479, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_7, prime_fiftyFourAZ_5783, prime_fiftyFourAZ_167071, prime_fiftyFourAZ_970780183, prime_fiftyFourAZ_1389114479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526450 : Nat.totient 63842411741552402445613526450 = 25296053694275189193984000000 := by
  rw [← show ((([(2, 1), (5, 2), (191, 1), (251, 1), (6271, 1), (13217, 1), (481513, 1), (667351259, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_191, prime_fiftyFourAZ_251, prime_fiftyFourAZ_6271, prime_fiftyFourAZ_13217, prime_fiftyFourAZ_481513, prime_fiftyFourAZ_667351259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526451 : Nat.totient 63842411741552402445613526451 = 40057942262304457612162009728 := by
  rw [← show ((([(3, 1), (17, 1), (963499, 1), (1299235385747572180099, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_17, prime_fiftyFourAZ_963499, prime_fiftyFourAZ_1299235385747572180099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526452 : Nat.totient 63842411741552402445613526452 = 29462551637694863240966400000 := by
  rw [← show ((([(2, 2), (13, 2), (9281, 1), (14626967, 1), (695686433921251, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_13, prime_fiftyFourAZ_9281, prime_fiftyFourAZ_14626967, prime_fiftyFourAZ_695686433921251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526453 : Nat.totient 63842411741552402445613526453 = 62083508434913710499453497344 := by
  rw [← show ((([(53, 1), (113, 1), (5026873, 1), (2120591705772817049, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_53, prime_fiftyFourAZ_113, prime_fiftyFourAZ_5026873, prime_fiftyFourAZ_2120591705772817049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526454 : Nat.totient 63842411741552402445613526454 = 21069986901359321511017571456 := by
  rw [← show ((([(2, 1), (3, 3), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_103, prime_fiftyFourAZ_5009, prime_fiftyFourAZ_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526455 : Nat.totient 63842411741552402445613526455 = 46408850187218662128330148000 := by
  rw [← show ((([(5, 1), (11, 1), (2111, 1), (549867893213491257444671, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_11, prime_fiftyFourAZ_2111, prime_fiftyFourAZ_549867893213491257444671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526456 : Nat.totient 63842411741552402445613526456 = 27359838565307590522716316800 := by
  rw [← show ((([(2, 3), (7, 1), (32051, 1), (80149, 1), (443794142129759999, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_7, prime_fiftyFourAZ_32051, prime_fiftyFourAZ_80149, prime_fiftyFourAZ_443794142129759999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526457 : Nat.totient 63842411741552402445613526457 = 40316837148380189731392115200 := by
  rw [← show ((([(3, 1), (19, 1), (8713, 1), (712477, 1), (23415331, 1), (7705406671, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_19, prime_fiftyFourAZ_8713, prime_fiftyFourAZ_712477, prime_fiftyFourAZ_23415331, prime_fiftyFourAZ_7705406671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526458 : Nat.totient 63842411741552402445613526458 = 30820474633852883939261702400 := by
  rw [← show ((([(2, 1), (29, 1), (1100731236923317283545060801, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_29, prime_fiftyFourAZ_1100731236923317283545060801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526459 : Nat.totient 63842411741552402445613526459 = 62702811440320549027933325280 := by
  rw [← show ((([(59, 1), (1091, 1), (5774742229, 1), (171751255104959, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_59, prime_fiftyFourAZ_1091, prime_fiftyFourAZ_5774742229, prime_fiftyFourAZ_171751255104959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526460 : Nat.totient 63842411741552402445613526460 = 16872863180679073406038671360 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (139, 1), (577, 1), (2303321, 1), (5759873610810107, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_139, prime_fiftyFourAZ_577, prime_fiftyFourAZ_2303321, prime_fiftyFourAZ_5759873610810107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526461 : Nat.totient 63842411741552402445613526461 = 62777702391708804246078410880 := by
  rw [← show ((([(61, 1), (3467, 1), (295575079417, 1), (1021310491259, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_61, prime_fiftyFourAZ_3467, prime_fiftyFourAZ_295575079417, prime_fiftyFourAZ_1021310491259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526462 : Nat.totient 63842411741552402445613526462 = 30456313953024766986380779200 := by
  rw [← show ((([(2, 1), (31, 1), (71, 1), (361727, 1), (40093901583788580553, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_31, prime_fiftyFourAZ_71, prime_fiftyFourAZ_361727, prime_fiftyFourAZ_40093901583788580553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526463 : Nat.totient 63842411741552402445613526463 = 36366060633750133416730638720 := by
  rw [← show ((([(3, 2), (7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_7, prime_fiftyFourAZ_331, prime_fiftyFourAZ_7129, prime_fiftyFourAZ_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526464 : Nat.totient 63842411741552402445613526464 = 31562540415127736437376870400 := by
  rw [← show ((([(2, 6), (89, 1), (142723051, 1), (78531733309302509, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_89, prime_fiftyFourAZ_142723051, prime_fiftyFourAZ_78531733309302509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526465 : Nat.totient 63842411741552402445613526465 = 47130690565946679924517671936 := by
  rw [← show ((([(5, 1), (13, 1), (3257, 1), (301563079481128940958473, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_13, prime_fiftyFourAZ_3257, prime_fiftyFourAZ_301563079481128940958473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526466 : Nat.totient 63842411741552402445613526466 = 19216029111215955730747645440 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (149, 1), (60793, 1), (106788750604720147493, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_11, prime_fiftyFourAZ_149, prime_fiftyFourAZ_60793, prime_fiftyFourAZ_106788750604720147493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526467 : Nat.totient 63842411741552402445613526467 = 63034279947355536591871583016 := by
  rw [← show ((([(79, 1), (808131794196865853741943373, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_79, prime_fiftyFourAZ_808131794196865853741943373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526468 : Nat.totient 63842411741552402445613526468 = 30043258165272488428651516544 := by
  rw [← show ((([(2, 2), (17, 1), (130787, 1), (7178534534772569414123, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_17, prime_fiftyFourAZ_130787, prime_fiftyFourAZ_7178534534772569414123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526469 : Nat.totient 63842411741552402445613526469 = 40710979059287999269447487408 := by
  rw [← show ((([(3, 1), (23, 1), (328103, 1), (2820005742344536930967, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_23, prime_fiftyFourAZ_328103, prime_fiftyFourAZ_2820005742344536930967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526470 : Nat.totient 63842411741552402445613526470 = 21888822664382070110504749056 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (5188849, 1), (175768162351756354129, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_7, prime_fiftyFourAZ_5188849, prime_fiftyFourAZ_175768162351756354129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526471 : Nat.totient 63842411741552402445613526471 = 63539840113781452083249363000 := by
  rw [← show ((([(211, 1), (66463571, 1), (4552428754707023791, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_211, prime_fiftyFourAZ_66463571, prime_fiftyFourAZ_4552428754707023791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526472 : Nat.totient 63842411741552402445613526472 = 21240739924839212415211929600 := by
  rw [← show ((([(2, 3), (3, 2), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_769, prime_fiftyFourAZ_2143, prime_fiftyFourAZ_8597, prime_fiftyFourAZ_9792301, prime_fiftyFourAZ_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526473 : Nat.totient 63842411741552402445613526473 = 63318075748596506122120281600 := by
  rw [← show ((([(127, 1), (2927, 1), (2086950601, 1), (82294473700337, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_127, prime_fiftyFourAZ_2927, prime_fiftyFourAZ_2086950601, prime_fiftyFourAZ_82294473700337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526474 : Nat.totient 63842411741552402445613526474 = 31058405278286565959589765312 := by
  rw [← show ((([(2, 1), (37, 1), (475637, 1), (1813852357585221913373, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_37, prime_fiftyFourAZ_475637, prime_fiftyFourAZ_1813852357585221913373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526475 : Nat.totient 63842411741552402445613526475 = 34047891999589635537105225600 := by
  rw [← show ((([(3, 1), (5, 2), (24421, 1), (34856564291144180525293, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_24421, prime_fiftyFourAZ_34856564291144180525293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526476 : Nat.totient 63842411741552402445613526476 = 30241141693331253337698483600 := by
  rw [← show ((([(2, 2), (19, 1), (42559471, 1), (19737833053457806831, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_19, prime_fiftyFourAZ_42559471, prime_fiftyFourAZ_19737833053457806831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526477 : Nat.totient 63842411741552402445613526477 = 49747333824586287619958592000 := by
  rw [← show ((([(7, 1), (11, 1), (829122230409771460332643201, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_7, prime_fiftyFourAZ_11, prime_fiftyFourAZ_829122230409771460332643201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526478 : Nat.totient 63842411741552402445613526478 = 19642109203772277142556368896 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (11489, 1), (71241401185919644928609, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_13, prime_fiftyFourAZ_11489, prime_fiftyFourAZ_71241401185919644928609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526479 : Nat.totient 63842411741552402445613526479 = 63741002088043711326921727104 := by
  rw [← show ((([(907, 1), (3359, 1), (5297, 1), (3956052268000347139, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_907, prime_fiftyFourAZ_3359, prime_fiftyFourAZ_5297, prime_fiftyFourAZ_3956052268000347139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526480 : Nat.totient 63842411741552402445613526480 = 25511815284689060173349978112 := by
  rw [← show ((([(2, 4), (5, 1), (2377, 1), (3089, 1), (4157, 1), (6528503, 1), (4004779187, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_2377, prime_fiftyFourAZ_3089, prime_fiftyFourAZ_4157, prime_fiftyFourAZ_6528503, prime_fiftyFourAZ_4004779187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526481 : Nat.totient 63842411741552402445613526481 = 42431842690044270627894912000 := by
  rw [← show ((([(3, 4), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_421, prime_fiftyFourAZ_1483, prime_fiftyFourAZ_2072201, prime_fiftyFourAZ_2567179, prime_fiftyFourAZ_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526482 : Nat.totient 63842411741552402445613526482 = 31139364915476014942248355200 := by
  rw [← show ((([(2, 1), (41, 1), (9587, 1), (1173541, 1), (69201329442777503, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_41, prime_fiftyFourAZ_9587, prime_fiftyFourAZ_1173541, prime_fiftyFourAZ_69201329442777503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526483 : Nat.totient 63842411741552402445613526483 = 63827470854180169259925337440 := by
  rw [← show ((([(4273, 1), (14940887372233185688184771, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_4273, prime_fiftyFourAZ_14940887372233185688184771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526484 : Nat.totient 63842411741552402445613526484 = 18174838203281357432562309120 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (277, 1), (6810796141, 1), (402858330250993, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_7, prime_fiftyFourAZ_277, prime_fiftyFourAZ_6810796141, prime_fiftyFourAZ_402858330250993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526485 : Nat.totient 63842411741552402445613526485 = 48059490413156761491218472960 := by
  rw [← show ((([(5, 1), (17, 1), (5227, 1), (53849, 1), (37279157, 1), (71580402031, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_17, prime_fiftyFourAZ_5227, prime_fiftyFourAZ_53849, prime_fiftyFourAZ_37279157, prime_fiftyFourAZ_71580402031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526486 : Nat.totient 63842411741552402445613526486 = 30676436372142754742255616000 := by
  rw [← show ((([(2, 1), (43, 1), (109, 1), (151, 1), (4993, 1), (5443, 1), (1659615521571361, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_43, prime_fiftyFourAZ_109, prime_fiftyFourAZ_151, prime_fiftyFourAZ_4993, prime_fiftyFourAZ_5443, prime_fiftyFourAZ_1659615521571361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526487 : Nat.totient 63842411741552402445613526487 = 41087263201206624831950492160 := by
  rw [← show ((([(3, 1), (29, 1), (6131, 1), (126749873, 1), (944302595030827, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_29, prime_fiftyFourAZ_6131, prime_fiftyFourAZ_126749873, prime_fiftyFourAZ_944302595030827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526488 : Nat.totient 63842411741552402445613526488 = 29019278064342001111642511600 := by
  rw [← show ((([(2, 3), (11, 2), (65952904691686366162823891, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_11, prime_fiftyFourAZ_65952904691686366162823891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526489 : Nat.totient 63842411741552402445613526489 = 63842411741552402445613526488 := by
  rw [← show ((([(63842411741552402445613526489, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_63842411741552402445613526489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526490 : Nat.totient 63842411741552402445613526490 = 16941101785182382994115471360 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_5, prime_fiftyFourAZ_281, prime_fiftyFourAZ_739, prime_fiftyFourAZ_3540386347, prime_fiftyFourAZ_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526491 : Nat.totient 63842411741552402445613526491 = 49653325503180875447203921920 := by
  rw [← show ((([(7, 1), (13, 1), (97, 1), (197, 1), (587, 1), (478727, 1), (130648343779361, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_7, prime_fiftyFourAZ_13, prime_fiftyFourAZ_97, prime_fiftyFourAZ_197, prime_fiftyFourAZ_587, prime_fiftyFourAZ_478727, prime_fiftyFourAZ_130648343779361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526492 : Nat.totient 63842411741552402445613526492 = 30533325928193455303357090560 := by
  rw [← show ((([(2, 2), (23, 1), (24289169, 1), (180464111, 1), (158313501439, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_23, prime_fiftyFourAZ_24289169, prime_fiftyFourAZ_180464111, prime_fiftyFourAZ_158313501439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526493 : Nat.totient 63842411741552402445613526493 = 41188652736485420932653888000 := by
  rw [← show ((([(3, 1), (31, 1), (686477545608090348877564801, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_31, prime_fiftyFourAZ_686477545608090348877564801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526494 : Nat.totient 63842411741552402445613526494 = 31223244728606109644017050552 := by
  rw [← show ((([(2, 1), (47, 1), (1663, 1), (408403242931592497828927, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_47, prime_fiftyFourAZ_1663, prime_fiftyFourAZ_408403242931592497828927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526495 : Nat.totient 63842411741552402445613526495 = 48045482184958373041605504000 := by
  rw [← show ((([(5, 1), (19, 1), (181, 1), (659, 1), (15058601, 1), (374142517230199, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_5, prime_fiftyFourAZ_19, prime_fiftyFourAZ_181, prime_fiftyFourAZ_659, prime_fiftyFourAZ_15058601, prime_fiftyFourAZ_374142517230199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526496 : Nat.totient 63842411741552402445613526496 = 21279982661105504751925601280 := by
  rw [← show ((([(2, 5), (3, 1), (25913, 1), (1731666887, 1), (14820266192971, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_3, prime_fiftyFourAZ_25913, prime_fiftyFourAZ_1731666887, prime_fiftyFourAZ_14820266192971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526497 : Nat.totient 63842411741552402445613526497 = 63842355072179832659079880960 := by
  rw [← show ((([(1126577, 1), (56669372569786532518961, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_1126577, prime_fiftyFourAZ_56669372569786532518961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526498 : Nat.totient 63842411741552402445613526498 = 27361032255341416165250258304 := by
  rw [← show ((([(2, 1), (7, 2), (20294777, 1), (32099548619639871113, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_7, prime_fiftyFourAZ_20294777, prime_fiftyFourAZ_32099548619639871113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526499 : Nat.totient 63842411741552402445613526499 = 38691778006785699526546146240 := by
  rw [← show ((([(3, 2), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_3, prime_fiftyFourAZ_11, prime_fiftyFourAZ_97327, prime_fiftyFourAZ_208223, prime_fiftyFourAZ_4129087, prime_fiftyFourAZ_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftyFourAZ_63842411741552402445613526500 : Nat.totient 63842411741552402445613526500 = 25536964695751822673021676000 := by
  rw [← show ((([(2, 2), (5, 3), (29382133091, 1), (4345662143985583, 1)] : List FactorBlock).map factorBlockValue).prod) = 63842411741552402445613526500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftyFourAZ_2, prime_fiftyFourAZ_5, prime_fiftyFourAZ_29382133091, prime_fiftyFourAZ_4345662143985583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftyFourAZ : certifiedKill 1 63842411741552402445613526399 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftyFourAZ_63842411741552402445613526400, phi_fiftyFourAZ_63842411741552402445613526401, phi_fiftyFourAZ_63842411741552402445613526402,
    phi_fiftyFourAZ_63842411741552402445613526403, phi_fiftyFourAZ_63842411741552402445613526404, phi_fiftyFourAZ_63842411741552402445613526405,
    phi_fiftyFourAZ_63842411741552402445613526406, phi_fiftyFourAZ_63842411741552402445613526407, phi_fiftyFourAZ_63842411741552402445613526408,
    phi_fiftyFourAZ_63842411741552402445613526409, phi_fiftyFourAZ_63842411741552402445613526410, phi_fiftyFourAZ_63842411741552402445613526411,
    phi_fiftyFourAZ_63842411741552402445613526412, phi_fiftyFourAZ_63842411741552402445613526413, phi_fiftyFourAZ_63842411741552402445613526414,
    phi_fiftyFourAZ_63842411741552402445613526415, phi_fiftyFourAZ_63842411741552402445613526416, phi_fiftyFourAZ_63842411741552402445613526417,
    phi_fiftyFourAZ_63842411741552402445613526418, phi_fiftyFourAZ_63842411741552402445613526419, phi_fiftyFourAZ_63842411741552402445613526420,
    phi_fiftyFourAZ_63842411741552402445613526421, phi_fiftyFourAZ_63842411741552402445613526422, phi_fiftyFourAZ_63842411741552402445613526423,
    phi_fiftyFourAZ_63842411741552402445613526424, phi_fiftyFourAZ_63842411741552402445613526425, phi_fiftyFourAZ_63842411741552402445613526426,
    phi_fiftyFourAZ_63842411741552402445613526427, phi_fiftyFourAZ_63842411741552402445613526428, phi_fiftyFourAZ_63842411741552402445613526429,
    phi_fiftyFourAZ_63842411741552402445613526430, phi_fiftyFourAZ_63842411741552402445613526431, phi_fiftyFourAZ_63842411741552402445613526432,
    phi_fiftyFourAZ_63842411741552402445613526433, phi_fiftyFourAZ_63842411741552402445613526434, phi_fiftyFourAZ_63842411741552402445613526435,
    phi_fiftyFourAZ_63842411741552402445613526436, phi_fiftyFourAZ_63842411741552402445613526437, phi_fiftyFourAZ_63842411741552402445613526438,
    phi_fiftyFourAZ_63842411741552402445613526439, phi_fiftyFourAZ_63842411741552402445613526440, phi_fiftyFourAZ_63842411741552402445613526441,
    phi_fiftyFourAZ_63842411741552402445613526442, phi_fiftyFourAZ_63842411741552402445613526443, phi_fiftyFourAZ_63842411741552402445613526444,
    phi_fiftyFourAZ_63842411741552402445613526445, phi_fiftyFourAZ_63842411741552402445613526446, phi_fiftyFourAZ_63842411741552402445613526447,
    phi_fiftyFourAZ_63842411741552402445613526448, phi_fiftyFourAZ_63842411741552402445613526449, phi_fiftyFourAZ_63842411741552402445613526450,
    phi_fiftyFourAZ_63842411741552402445613526451, phi_fiftyFourAZ_63842411741552402445613526452, phi_fiftyFourAZ_63842411741552402445613526453,
    phi_fiftyFourAZ_63842411741552402445613526454, phi_fiftyFourAZ_63842411741552402445613526455, phi_fiftyFourAZ_63842411741552402445613526456,
    phi_fiftyFourAZ_63842411741552402445613526457, phi_fiftyFourAZ_63842411741552402445613526458, phi_fiftyFourAZ_63842411741552402445613526459,
    phi_fiftyFourAZ_63842411741552402445613526460, phi_fiftyFourAZ_63842411741552402445613526461, phi_fiftyFourAZ_63842411741552402445613526462,
    phi_fiftyFourAZ_63842411741552402445613526463, phi_fiftyFourAZ_63842411741552402445613526464, phi_fiftyFourAZ_63842411741552402445613526465,
    phi_fiftyFourAZ_63842411741552402445613526466, phi_fiftyFourAZ_63842411741552402445613526467, phi_fiftyFourAZ_63842411741552402445613526468,
    phi_fiftyFourAZ_63842411741552402445613526469, phi_fiftyFourAZ_63842411741552402445613526470, phi_fiftyFourAZ_63842411741552402445613526471,
    phi_fiftyFourAZ_63842411741552402445613526472, phi_fiftyFourAZ_63842411741552402445613526473, phi_fiftyFourAZ_63842411741552402445613526474,
    phi_fiftyFourAZ_63842411741552402445613526475, phi_fiftyFourAZ_63842411741552402445613526476, phi_fiftyFourAZ_63842411741552402445613526477,
    phi_fiftyFourAZ_63842411741552402445613526478, phi_fiftyFourAZ_63842411741552402445613526479, phi_fiftyFourAZ_63842411741552402445613526480,
    phi_fiftyFourAZ_63842411741552402445613526481, phi_fiftyFourAZ_63842411741552402445613526482, phi_fiftyFourAZ_63842411741552402445613526483,
    phi_fiftyFourAZ_63842411741552402445613526484, phi_fiftyFourAZ_63842411741552402445613526485, phi_fiftyFourAZ_63842411741552402445613526486,
    phi_fiftyFourAZ_63842411741552402445613526487, phi_fiftyFourAZ_63842411741552402445613526488, phi_fiftyFourAZ_63842411741552402445613526489,
    phi_fiftyFourAZ_63842411741552402445613526490, phi_fiftyFourAZ_63842411741552402445613526491, phi_fiftyFourAZ_63842411741552402445613526492,
    phi_fiftyFourAZ_63842411741552402445613526493, phi_fiftyFourAZ_63842411741552402445613526494, phi_fiftyFourAZ_63842411741552402445613526495,
    phi_fiftyFourAZ_63842411741552402445613526496, phi_fiftyFourAZ_63842411741552402445613526497, phi_fiftyFourAZ_63842411741552402445613526498,
    phi_fiftyFourAZ_63842411741552402445613526499, phi_fiftyFourAZ_63842411741552402445613526500
  ]

end TotientTailPeriodKiller
end Erdos249257
