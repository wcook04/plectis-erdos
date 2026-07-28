import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyEightCHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyEightCHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyEightCHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyEightCHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyEightCHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyEightCHFastPow a n * eightyEightCHFastPow a n * a else eightyEightCHFastPow a n * eightyEightCHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyEightCH_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyEightCH_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyEightCH_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyEightCH_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyEightCH_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyEightCH_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyEightCH_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyEightCH_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyEightCH_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyEightCH_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyEightCH_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyEightCH_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyEightCH_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyEightCH_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyEightCH_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyEightCH_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyEightCH_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyEightCH_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyEightCH_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyEightCH_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyEightCH_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyEightCH_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyEightCH_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyEightCH_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyEightCH_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyEightCH_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyEightCH_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyEightCH_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyEightCH_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyEightCH_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyEightCH_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyEightCH_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyEightCH_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyEightCH_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyEightCH_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyEightCH_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyEightCH_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightyEightCH_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyEightCH_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyEightCH_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyEightCH_179 : Nat.Prime 179 := by norm_num

private theorem prime_eightyEightCH_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyEightCH_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightyEightCH_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyEightCH_197 : Nat.Prime 197 := by norm_num

private theorem prime_eightyEightCH_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightyEightCH_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyEightCH_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightyEightCH_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyEightCH_229 : Nat.Prime 229 := by norm_num

private theorem prime_eightyEightCH_233 : Nat.Prime 233 := by norm_num

private theorem prime_eightyEightCH_239 : Nat.Prime 239 := by norm_num

private theorem prime_eightyEightCH_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyEightCH_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyEightCH_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightyEightCH_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightyEightCH_307 : Nat.Prime 307 := by norm_num

private theorem prime_eightyEightCH_311 : Nat.Prime 311 := by norm_num

private theorem prime_eightyEightCH_313 : Nat.Prime 313 := by norm_num

private theorem prime_eightyEightCH_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyEightCH_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightyEightCH_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightyEightCH_349 : Nat.Prime 349 := by norm_num

private theorem prime_eightyEightCH_353 : Nat.Prime 353 := by norm_num

private theorem prime_eightyEightCH_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyEightCH_389 : Nat.Prime 389 := by norm_num

private theorem prime_eightyEightCH_419 : Nat.Prime 419 := by norm_num

private theorem prime_eightyEightCH_431 : Nat.Prime 431 := by norm_num

private theorem prime_eightyEightCH_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightyEightCH_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightyEightCH_463 : Nat.Prime 463 := by norm_num

private theorem prime_eightyEightCH_487 : Nat.Prime 487 := by norm_num

private theorem prime_eightyEightCH_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightyEightCH_503 : Nat.Prime 503 := by norm_num

private theorem prime_eightyEightCH_509 : Nat.Prime 509 := by norm_num

private theorem prime_eightyEightCH_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyEightCH_541 : Nat.Prime 541 := by norm_num

private theorem prime_eightyEightCH_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightyEightCH_557 : Nat.Prime 557 := by norm_num

private theorem prime_eightyEightCH_577 : Nat.Prime 577 := by norm_num

private theorem prime_eightyEightCH_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightyEightCH_593 : Nat.Prime 593 := by norm_num

private theorem prime_eightyEightCH_599 : Nat.Prime 599 := by norm_num

private theorem prime_eightyEightCH_607 : Nat.Prime 607 := by norm_num

private theorem prime_eightyEightCH_617 : Nat.Prime 617 := by norm_num

private theorem prime_eightyEightCH_619 : Nat.Prime 619 := by norm_num

private theorem prime_eightyEightCH_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightyEightCH_677 : Nat.Prime 677 := by norm_num

private theorem prime_eightyEightCH_691 : Nat.Prime 691 := by norm_num

private theorem prime_eightyEightCH_719 : Nat.Prime 719 := by norm_num

private theorem prime_eightyEightCH_727 : Nat.Prime 727 := by norm_num

private theorem prime_eightyEightCH_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightyEightCH_761 : Nat.Prime 761 := by norm_num

private theorem prime_eightyEightCH_769 : Nat.Prime 769 := by norm_num

private theorem prime_eightyEightCH_773 : Nat.Prime 773 := by norm_num

private theorem prime_eightyEightCH_797 : Nat.Prime 797 := by norm_num

private theorem prime_eightyEightCH_809 : Nat.Prime 809 := by norm_num

private theorem prime_eightyEightCH_823 : Nat.Prime 823 := by norm_num

private theorem prime_eightyEightCH_853 : Nat.Prime 853 := by norm_num

private theorem prime_eightyEightCH_881 : Nat.Prime 881 := by norm_num

private theorem prime_eightyEightCH_911 : Nat.Prime 911 := by norm_num

private theorem prime_eightyEightCH_971 : Nat.Prime 971 := by norm_num

private theorem prime_eightyEightCH_983 : Nat.Prime 983 := by norm_num

private theorem prime_eightyEightCH_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_eightyEightCH_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_eightyEightCH_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_eightyEightCH_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_eightyEightCH_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_eightyEightCH_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_eightyEightCH_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_eightyEightCH_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_eightyEightCH_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_eightyEightCH_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightyEightCH_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_eightyEightCH_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_eightyEightCH_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_eightyEightCH_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_eightyEightCH_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_eightyEightCH_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_eightyEightCH_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_eightyEightCH_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_eightyEightCH_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_eightyEightCH_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_eightyEightCH_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_eightyEightCH_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_eightyEightCH_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_eightyEightCH_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_eightyEightCH_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_eightyEightCH_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_eightyEightCH_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_eightyEightCH_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_eightyEightCH_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_eightyEightCH_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_eightyEightCH_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_eightyEightCH_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_eightyEightCH_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_eightyEightCH_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_eightyEightCH_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_eightyEightCH_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_eightyEightCH_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_eightyEightCH_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_eightyEightCH_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_eightyEightCH_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_eightyEightCH_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_eightyEightCH_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_eightyEightCH_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_eightyEightCH_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_eightyEightCH_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_eightyEightCH_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_eightyEightCH_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_eightyEightCH_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_eightyEightCH_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_eightyEightCH_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_eightyEightCH_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_eightyEightCH_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_eightyEightCH_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_eightyEightCH_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_eightyEightCH_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_eightyEightCH_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_eightyEightCH_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_eightyEightCH_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_eightyEightCH_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_eightyEightCH_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_eightyEightCH_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_eightyEightCH_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_eightyEightCH_3557 : Nat.Prime 3557 := by norm_num

private theorem prime_eightyEightCH_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_eightyEightCH_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_eightyEightCH_3793 : Nat.Prime 3793 := by norm_num

private theorem prime_eightyEightCH_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_eightyEightCH_4201 : Nat.Prime 4201 := by norm_num

private theorem prime_eightyEightCH_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_eightyEightCH_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_eightyEightCH_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_eightyEightCH_4591 : Nat.Prime 4591 := by norm_num

private theorem prime_eightyEightCH_4639 : Nat.Prime 4639 := by norm_num

private theorem prime_eightyEightCH_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_eightyEightCH_4831 : Nat.Prime 4831 := by norm_num

private theorem prime_eightyEightCH_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_eightyEightCH_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_eightyEightCH_5077 : Nat.Prime 5077 := by norm_num

private theorem prime_eightyEightCH_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_eightyEightCH_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_eightyEightCH_5431 : Nat.Prime 5431 := by norm_num

private theorem prime_eightyEightCH_5443 : Nat.Prime 5443 := by norm_num

private theorem prime_eightyEightCH_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_eightyEightCH_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_eightyEightCH_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_eightyEightCH_5869 : Nat.Prime 5869 := by norm_num

private theorem prime_eightyEightCH_6067 : Nat.Prime 6067 := by norm_num

private theorem prime_eightyEightCH_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_eightyEightCH_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_eightyEightCH_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_eightyEightCH_6599 : Nat.Prime 6599 := by norm_num

private theorem prime_eightyEightCH_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_eightyEightCH_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_eightyEightCH_7019 : Nat.Prime 7019 := by norm_num

private theorem prime_eightyEightCH_7193 : Nat.Prime 7193 := by norm_num

private theorem prime_eightyEightCH_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_eightyEightCH_7759 : Nat.Prime 7759 := by norm_num

private theorem prime_eightyEightCH_8069 : Nat.Prime 8069 := by norm_num

private theorem prime_eightyEightCH_8117 : Nat.Prime 8117 := by norm_num

private theorem prime_eightyEightCH_8161 : Nat.Prime 8161 := by norm_num

private theorem prime_eightyEightCH_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_eightyEightCH_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_eightyEightCH_8837 : Nat.Prime 8837 := by norm_num

private theorem prime_eightyEightCH_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_eightyEightCH_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_eightyEightCH_9511 : Nat.Prime 9511 := by norm_num

private theorem prime_eightyEightCH_9749 : Nat.Prime 9749 := by norm_num

private theorem prime_eightyEightCH_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_eightyEightCH_10429 : Nat.Prime 10429 := by norm_num

private theorem prime_eightyEightCH_10667 : Nat.Prime 10667 := by norm_num

private theorem prime_eightyEightCH_10837 : Nat.Prime 10837 := by norm_num

private theorem prime_eightyEightCH_11083 : Nat.Prime 11083 := by norm_num

private theorem prime_eightyEightCH_11149 : Nat.Prime 11149 := by norm_num

private theorem prime_eightyEightCH_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_eightyEightCH_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_eightyEightCH_12301 : Nat.Prime 12301 := by norm_num

private theorem prime_eightyEightCH_12347 : Nat.Prime 12347 := by norm_num

private theorem prime_eightyEightCH_12569 : Nat.Prime 12569 := by norm_num

private theorem prime_eightyEightCH_13291 : Nat.Prime 13291 := by norm_num

private theorem prime_eightyEightCH_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_eightyEightCH_14173 : Nat.Prime 14173 := by norm_num

private theorem prime_eightyEightCH_14293 : Nat.Prime 14293 := by norm_num

private theorem prime_eightyEightCH_14851 : Nat.Prime 14851 := by norm_num

private theorem prime_eightyEightCH_15259 : Nat.Prime 15259 := by norm_num

private theorem prime_eightyEightCH_15511 : Nat.Prime 15511 := by norm_num

private theorem prime_eightyEightCH_16369 : Nat.Prime 16369 := by norm_num

private theorem prime_eightyEightCH_16427 : Nat.Prime 16427 := by norm_num

private theorem prime_eightyEightCH_16879 : Nat.Prime 16879 := by norm_num

private theorem prime_eightyEightCH_17657 : Nat.Prime 17657 := by norm_num

private theorem prime_eightyEightCH_17921 : Nat.Prime 17921 := by norm_num

private theorem prime_eightyEightCH_19087 : Nat.Prime 19087 := by norm_num

private theorem prime_eightyEightCH_20849 : Nat.Prime 20849 := by norm_num

private theorem prime_eightyEightCH_20903 : Nat.Prime 20903 := by norm_num

private theorem prime_eightyEightCH_20947 : Nat.Prime 20947 := by norm_num

private theorem prime_eightyEightCH_21599 : Nat.Prime 21599 := by norm_num

private theorem prime_eightyEightCH_22621 : Nat.Prime 22621 := by norm_num

private theorem prime_eightyEightCH_23879 : Nat.Prime 23879 := by norm_num

private theorem prime_eightyEightCH_24239 : Nat.Prime 24239 := by norm_num

private theorem prime_eightyEightCH_25439 : Nat.Prime 25439 := by norm_num

private theorem prime_eightyEightCH_25943 : Nat.Prime 25943 := by norm_num

private theorem prime_eightyEightCH_26647 : Nat.Prime 26647 := by norm_num

private theorem prime_eightyEightCH_27527 : Nat.Prime 27527 := by norm_num

private theorem prime_eightyEightCH_28111 : Nat.Prime 28111 := by norm_num

private theorem prime_eightyEightCH_28547 : Nat.Prime 28547 := by norm_num

private theorem prime_eightyEightCH_30839 : Nat.Prime 30839 := by norm_num

private theorem prime_eightyEightCH_31649 : Nat.Prime 31649 := by norm_num

private theorem prime_eightyEightCH_31859 : Nat.Prime 31859 := by norm_num

private theorem prime_eightyEightCH_36209 : Nat.Prime 36209 := by norm_num

private theorem prime_eightyEightCH_36229 : Nat.Prime 36229 := by norm_num

private theorem prime_eightyEightCH_38707 : Nat.Prime 38707 := by norm_num

private theorem prime_eightyEightCH_40639 : Nat.Prime 40639 := by norm_num

private theorem prime_eightyEightCH_40939 : Nat.Prime 40939 := by norm_num

private theorem prime_eightyEightCH_41611 : Nat.Prime 41611 := by norm_num

private theorem prime_eightyEightCH_46261 : Nat.Prime 46261 := by norm_num

private theorem prime_eightyEightCH_47441 : Nat.Prime 47441 := by norm_num

private theorem prime_eightyEightCH_47701 : Nat.Prime 47701 := by norm_num

private theorem prime_eightyEightCH_48809 : Nat.Prime 48809 := by norm_num

private theorem prime_eightyEightCH_48823 : Nat.Prime 48823 := by norm_num

private theorem prime_eightyEightCH_50273 : Nat.Prime 50273 := by norm_num

private theorem prime_eightyEightCH_52639 : Nat.Prime 52639 := by norm_num

private theorem prime_eightyEightCH_53881 : Nat.Prime 53881 := by norm_num

private theorem prime_eightyEightCH_54361 : Nat.Prime 54361 := by norm_num

private theorem prime_eightyEightCH_56921 : Nat.Prime 56921 := by norm_num

private theorem prime_eightyEightCH_57119 : Nat.Prime 57119 := by norm_num

private theorem prime_eightyEightCH_57917 : Nat.Prime 57917 := by norm_num

private theorem prime_eightyEightCH_58573 : Nat.Prime 58573 := by norm_num

private theorem prime_eightyEightCH_59221 : Nat.Prime 59221 := by norm_num

private theorem prime_eightyEightCH_63587 : Nat.Prime 63587 := by norm_num

private theorem prime_eightyEightCH_64793 : Nat.Prime 64793 := by norm_num

private theorem prime_eightyEightCH_66169 : Nat.Prime 66169 := by norm_num

private theorem prime_eightyEightCH_67577 : Nat.Prime 67577 := by norm_num

private theorem prime_eightyEightCH_68023 : Nat.Prime 68023 := by norm_num

private theorem prime_eightyEightCH_68543 : Nat.Prime 68543 := by norm_num

private theorem prime_eightyEightCH_72253 : Nat.Prime 72253 := by norm_num

private theorem prime_eightyEightCH_73721 : Nat.Prime 73721 := by norm_num

private theorem prime_eightyEightCH_80149 : Nat.Prime 80149 := by norm_num

private theorem prime_eightyEightCH_80239 : Nat.Prime 80239 := by norm_num

private theorem prime_eightyEightCH_81409 : Nat.Prime 81409 := by norm_num

private theorem prime_eightyEightCH_83063 : Nat.Prime 83063 := by norm_num

private theorem prime_eightyEightCH_86011 : Nat.Prime 86011 := by norm_num

private theorem prime_eightyEightCH_86381 : Nat.Prime 86381 := by norm_num

private theorem prime_eightyEightCH_86627 : Nat.Prime 86627 := by norm_num

private theorem prime_eightyEightCH_87719 : Nat.Prime 87719 := by norm_num

private theorem prime_eightyEightCH_90439 : Nat.Prime 90439 := by norm_num

private theorem prime_eightyEightCH_91141 : Nat.Prime 91141 := by norm_num

private theorem prime_eightyEightCH_94421 : Nat.Prime 94421 := by norm_num

private theorem prime_eightyEightCH_94889 : Nat.Prime 94889 := by norm_num

private theorem prime_eightyEightCH_104891 : Nat.Prime 104891 := by norm_num

private theorem prime_eightyEightCH_119747 : Nat.Prime 119747 := by norm_num

private theorem prime_eightyEightCH_123931 : Nat.Prime 123931 := by norm_num

private theorem prime_eightyEightCH_126473 : Nat.Prime 126473 := by norm_num

private theorem prime_eightyEightCH_127363 : Nat.Prime 127363 := by norm_num

private theorem prime_eightyEightCH_137957 : Nat.Prime 137957 := by norm_num

private theorem prime_eightyEightCH_140629 : Nat.Prime 140629 := by norm_num

private theorem prime_eightyEightCH_142039 : Nat.Prime 142039 := by norm_num

private theorem prime_eightyEightCH_157793 : Nat.Prime 157793 := by norm_num

private theorem prime_eightyEightCH_167341 : Nat.Prime 167341 := by norm_num

private theorem prime_eightyEightCH_172169 : Nat.Prime 172169 := by norm_num

private theorem prime_eightyEightCH_175129 : Nat.Prime 175129 := by norm_num

private theorem prime_eightyEightCH_178067 : Nat.Prime 178067 := by norm_num

private theorem prime_eightyEightCH_184081 : Nat.Prime 184081 := by norm_num

private theorem prime_eightyEightCH_201211 : Nat.Prime 201211 := by norm_num

private theorem prime_eightyEightCH_208513 : Nat.Prime 208513 := by norm_num

private theorem prime_eightyEightCH_209639 : Nat.Prime 209639 := by norm_num

private theorem prime_eightyEightCH_226409 : Nat.Prime 226409 := by norm_num

private theorem prime_eightyEightCH_232457 : Nat.Prime 232457 := by norm_num

private theorem prime_eightyEightCH_250499 : Nat.Prime 250499 := by norm_num

private theorem prime_eightyEightCH_251233 : Nat.Prime 251233 := by norm_num

private theorem prime_eightyEightCH_261463 : Nat.Prime 261463 := by norm_num

private theorem prime_eightyEightCH_264637 : Nat.Prime 264637 := by norm_num

private theorem prime_eightyEightCH_279967 : Nat.Prime 279967 := by norm_num

private theorem prime_eightyEightCH_281921 : Nat.Prime 281921 := by norm_num

private theorem prime_eightyEightCH_288817 : Nat.Prime 288817 := by norm_num

private theorem prime_eightyEightCH_289171 : Nat.Prime 289171 := by norm_num

private theorem prime_eightyEightCH_300317 : Nat.Prime 300317 := by norm_num

private theorem prime_eightyEightCH_317071 : Nat.Prime 317071 := by norm_num

private theorem prime_eightyEightCH_328127 : Nat.Prime 328127 := by norm_num

private theorem prime_eightyEightCH_341953 : Nat.Prime 341953 := by norm_num

private theorem prime_eightyEightCH_350351 : Nat.Prime 350351 := by norm_num

private theorem prime_eightyEightCH_355951 : Nat.Prime 355951 := by norm_num

private theorem prime_eightyEightCH_372943 : Nat.Prime 372943 := by norm_num

private theorem prime_eightyEightCH_385589 : Nat.Prime 385589 := by norm_num

private theorem prime_eightyEightCH_391627 : Nat.Prime 391627 := by norm_num

private theorem prime_eightyEightCH_405277 : Nat.Prime 405277 := by norm_num

private theorem prime_eightyEightCH_409523 : Nat.Prime 409523 := by norm_num

private theorem prime_eightyEightCH_414559 : Nat.Prime 414559 := by norm_num

private theorem prime_eightyEightCH_452077 : Nat.Prime 452077 := by norm_num

private theorem prime_eightyEightCH_470489 : Nat.Prime 470489 := by norm_num

private theorem prime_eightyEightCH_478207 : Nat.Prime 478207 := by norm_num

private theorem prime_eightyEightCH_478991 : Nat.Prime 478991 := by norm_num

private theorem prime_eightyEightCH_492883 : Nat.Prime 492883 := by norm_num

private theorem prime_eightyEightCH_510047 : Nat.Prime 510047 := by norm_num

private theorem prime_eightyEightCH_566047 : Nat.Prime 566047 := by norm_num

private theorem prime_eightyEightCH_594911 : Nat.Prime 594911 := by norm_num

private theorem prime_eightyEightCH_630997 : Nat.Prime 630997 := by norm_num

private theorem prime_eightyEightCH_687433 : Nat.Prime 687433 := by norm_num

private theorem prime_eightyEightCH_734549 : Nat.Prime 734549 := by norm_num

private theorem prime_eightyEightCH_740461 : Nat.Prime 740461 := by norm_num

private theorem prime_eightyEightCH_780397 : Nat.Prime 780397 := by norm_num

private theorem prime_eightyEightCH_790879 : Nat.Prime 790879 := by norm_num

private theorem prime_eightyEightCH_910171 : Nat.Prime 910171 := by norm_num

private theorem prime_eightyEightCH_965227 : Nat.Prime 965227 := by norm_num

private theorem prime_eightyEightCH_994457 : Nat.Prime 994457 := by norm_num

private theorem prime_eightyEightCH_1020101 : Nat.Prime 1020101 := by norm_num

private theorem prime_eightyEightCH_1186693 : Nat.Prime 1186693 := by norm_num

private theorem prime_eightyEightCH_1196537 : Nat.Prime 1196537 := by norm_num

private theorem prime_eightyEightCH_1209883 : Nat.Prime 1209883 := by norm_num

private theorem prime_eightyEightCH_1232069 : Nat.Prime 1232069 := by norm_num

private theorem prime_eightyEightCH_1289971 : Nat.Prime 1289971 := by norm_num

private theorem prime_eightyEightCH_1388053 : Nat.Prime 1388053 := by norm_num

private theorem prime_eightyEightCH_1550513 : Nat.Prime 1550513 := by norm_num

private theorem prime_eightyEightCH_1561601 : Nat.Prime 1561601 := by norm_num

private theorem prime_eightyEightCH_1584547 : Nat.Prime 1584547 := by norm_num

private theorem prime_eightyEightCH_1608583 : Nat.Prime 1608583 := by norm_num

private theorem prime_eightyEightCH_1811903 : Nat.Prime 1811903 := by norm_num

private theorem prime_eightyEightCH_2099441 : Nat.Prime 2099441 := by norm_num

private theorem prime_eightyEightCH_2179391 : Nat.Prime 2179391 := by norm_num

private theorem prime_eightyEightCH_2230549 : Nat.Prime 2230549 := by norm_num

private theorem prime_eightyEightCH_2439197 : Nat.Prime 2439197 := by norm_num

private theorem prime_eightyEightCH_2532007 : Nat.Prime 2532007 := by norm_num

private theorem prime_eightyEightCH_2545357 : Nat.Prime 2545357 := by norm_num

private theorem prime_eightyEightCH_2547689 : Nat.Prime 2547689 := by norm_num

private theorem prime_eightyEightCH_2576993 : Nat.Prime 2576993 := by norm_num

private theorem prime_eightyEightCH_2580997 : Nat.Prime 2580997 := by norm_num

private theorem prime_eightyEightCH_2591843 : Nat.Prime 2591843 := by norm_num

private theorem prime_eightyEightCH_2941891 : Nat.Prime 2941891 := by norm_num

private theorem prime_eightyEightCH_3081503 : Nat.Prime 3081503 := by norm_num

private theorem prime_eightyEightCH_3089377 : Nat.Prime 3089377 := by norm_num

private theorem prime_eightyEightCH_3405881 : Nat.Prime 3405881 := by norm_num

private theorem prime_eightyEightCH_3769453 : Nat.Prime 3769453 := by norm_num

private theorem prime_eightyEightCH_3880451 : Nat.Prime 3880451 := by norm_num

private theorem prime_eightyEightCH_3959129 : Nat.Prime 3959129 := by norm_num

private theorem prime_eightyEightCH_4119239 : Nat.Prime 4119239 := by norm_num

private theorem prime_eightyEightCH_4232827 : Nat.Prime 4232827 := by norm_num

private theorem prime_eightyEightCH_4351349 : Nat.Prime 4351349 := by norm_num

private theorem prime_eightyEightCH_4358927 : Nat.Prime 4358927 := by norm_num

private theorem prime_eightyEightCH_4436071 : Nat.Prime 4436071 := by norm_num

private theorem prime_eightyEightCH_4566941 : Nat.Prime 4566941 := by norm_num

private theorem prime_eightyEightCH_5132213 : Nat.Prime 5132213 := by norm_num

private theorem prime_eightyEightCH_5263003 : Nat.Prime 5263003 := by norm_num

private theorem prime_eightyEightCH_5338427 : Nat.Prime 5338427 := by norm_num

private theorem prime_eightyEightCH_5356567 : Nat.Prime 5356567 := by norm_num

private theorem prime_eightyEightCH_5446327 : Nat.Prime 5446327 := by norm_num

private theorem prime_eightyEightCH_5501057 : Nat.Prime 5501057 := by norm_num

private theorem prime_eightyEightCH_5510237 : Nat.Prime 5510237 := by norm_num

private theorem prime_eightyEightCH_5777621 : Nat.Prime 5777621 := by norm_num

private theorem prime_eightyEightCH_6278243 : Nat.Prime 6278243 := by norm_num

private theorem prime_eightyEightCH_6290827 : Nat.Prime 6290827 := by norm_num

private theorem prime_eightyEightCH_6443963 : Nat.Prime 6443963 := by norm_num

private theorem prime_eightyEightCH_6826271 : Nat.Prime 6826271 := by norm_num

private theorem prime_eightyEightCH_7156411 : Nat.Prime 7156411 := by norm_num

private theorem prime_eightyEightCH_7374749 : Nat.Prime 7374749 := by norm_num

private theorem prime_eightyEightCH_7455937 : Nat.Prime 7455937 := by norm_num

private theorem prime_eightyEightCH_7484333 : Nat.Prime 7484333 := by norm_num

private theorem prime_eightyEightCH_7493621 : Nat.Prime 7493621 := by norm_num

private theorem prime_eightyEightCH_7630979 : Nat.Prime 7630979 := by norm_num

private theorem prime_eightyEightCH_7755379 : Nat.Prime 7755379 := by norm_num

private theorem prime_eightyEightCH_7884529 : Nat.Prime 7884529 := by norm_num

private theorem prime_eightyEightCH_8454239 : Nat.Prime 8454239 := by norm_num

private theorem prime_eightyEightCH_8940539 : Nat.Prime 8940539 := by norm_num

private theorem prime_eightyEightCH_9071969 : Nat.Prime 9071969 := by norm_num

private theorem prime_eightyEightCH_9128123 : Nat.Prime 9128123 := by norm_num

private theorem prime_eightyEightCH_9229111 : Nat.Prime 9229111 := by norm_num

private theorem prime_eightyEightCH_9362747 : Nat.Prime 9362747 := by norm_num

private theorem prime_eightyEightCH_9467987 : Nat.Prime 9467987 := by norm_num

private theorem prime_eightyEightCH_10073923 : Nat.Prime 10073923 := by norm_num

private theorem prime_eightyEightCH_10284511 : Nat.Prime 10284511 := by norm_num

private theorem prime_eightyEightCH_10295123 : Nat.Prime 10295123 := by norm_num

private theorem prime_eightyEightCH_12826999 : Nat.Prime 12826999 := by norm_num

private theorem prime_eightyEightCH_13814831 : Nat.Prime 13814831 := by norm_num

private theorem prime_eightyEightCH_15719567 : Nat.Prime 15719567 := by norm_num

private theorem prime_eightyEightCH_16017601 : Nat.Prime 16017601 := by norm_num

private theorem prime_eightyEightCH_16627981 : Nat.Prime 16627981 := by norm_num

private theorem prime_eightyEightCH_19997827 : Nat.Prime 19997827 := by norm_num

private theorem prime_eightyEightCH_21100531 : Nat.Prime 21100531 := by norm_num

private theorem prime_eightyEightCH_21203771 : Nat.Prime 21203771 := by norm_num

private theorem prime_eightyEightCH_21432751 : Nat.Prime 21432751 := by norm_num

private theorem prime_eightyEightCH_23794487 : Nat.Prime 23794487 := by norm_num

private theorem prime_eightyEightCH_24758033 : Nat.Prime 24758033 := by norm_num

private theorem prime_eightyEightCH_25487599 : Nat.Prime 25487599 := by norm_num

private theorem prime_eightyEightCH_26324773 : Nat.Prime 26324773 := by norm_num

private theorem prime_eightyEightCH_31021517 : Nat.Prime 31021517 := by
  apply lucas_primality 31021517 (2 : ZMod 31021517)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7755379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7755379, 1)] : List FactorBlock).map factorBlockValue).prod) = 31021517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7755379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31021517) ^ 15510758 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31021517) ^ 4 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_33587233 : Nat.Prime 33587233 := by
  apply lucas_primality 33587233 (5 : ZMod 33587233)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (151, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (151, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 33587233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33587233) ^ 16793616 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33587233) ^ 11195744 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33587233) ^ 4798176 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33587233) ^ 222432 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 33587233) ^ 101472 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_35431397 : Nat.Prime 35431397 := by
  apply lucas_primality 35431397 (3 : ZMod 35431397)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (13, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (13, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) = 35431397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_8849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35431397) ^ 17715698 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35431397) ^ 5061628 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35431397) ^ 3221036 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35431397) ^ 2725492 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35431397) ^ 4004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_35608721 : Nat.Prime 35608721 := by
  apply lucas_primality 35608721 (6 : ZMod 35608721)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (63587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (63587, 1)] : List FactorBlock).map factorBlockValue).prod) = 35608721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_63587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 35608721) ^ 17804360 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 35608721) ^ 7121744 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 35608721) ^ 5086960 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 35608721) ^ 560 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_36815021 : Nat.Prime 36815021 := by
  apply lucas_primality 36815021 (2 : ZMod 36815021)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (167341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (167341, 1)] : List FactorBlock).map factorBlockValue).prod) = 36815021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_167341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36815021) ^ 18407510 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36815021) ^ 7363004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36815021) ^ 3346820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36815021) ^ 220 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_40332499 : Nat.Prime 40332499 := by
  apply lucas_primality 40332499 (7 : ZMod 40332499)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (547, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (547, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) = 40332499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_547
      · exact prime_eightyEightCH_12289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 40332499) ^ 20166249 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 40332499) ^ 13444166 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 40332499) ^ 73734 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 40332499) ^ 3282 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_42407543 : Nat.Prime 42407543 := by
  apply lucas_primality 42407543 (5 : ZMod 42407543)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21203771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21203771, 1)] : List FactorBlock).map factorBlockValue).prod) = 42407543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_21203771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 42407543) ^ 21203771 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42407543) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_44020219 : Nat.Prime 44020219 := by
  apply lucas_primality 44020219 (11 : ZMod 44020219)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (15511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (15511, 1)] : List FactorBlock).map factorBlockValue).prod) = 44020219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_15511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 44020219) ^ 22010109 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 44020219) ^ 14673406 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 44020219) ^ 4001838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 44020219) ^ 1023726 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 44020219) ^ 2838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_44959141 : Nat.Prime 44959141 := by
  apply lucas_primality 44959141 (7 : ZMod 44959141)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (101, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (101, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) = 44959141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_101
      · exact prime_eightyEightCH_2473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 44959141) ^ 22479570 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44959141) ^ 14986380 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44959141) ^ 8991828 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44959141) ^ 445140 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44959141) ^ 18180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_48667169 : Nat.Prime 48667169 := by
  apply lucas_primality 48667169 (3 : ZMod 48667169)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 2), (12569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 2), (12569, 1)] : List FactorBlock).map factorBlockValue).prod) = 48667169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_12569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48667169) ^ 24333584 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48667169) ^ 4424288 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 48667169) ^ 3872 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_49007171 : Nat.Prime 49007171 := by
  apply lucas_primality 49007171 (6 : ZMod 49007171)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (83063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (83063, 1)] : List FactorBlock).map factorBlockValue).prod) = 49007171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_83063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 49007171) ^ 24503585 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 49007171) ^ 9801434 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 49007171) ^ 830630 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 49007171) ^ 590 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_49292377 : Nat.Prime 49292377 := by
  apply lucas_primality 49292377 (10 : ZMod 49292377)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (59, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (59, 1), (4973, 1)] : List FactorBlock).map factorBlockValue).prod) = 49292377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_4973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 49292377) ^ 24646188 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 49292377) ^ 16430792 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 49292377) ^ 7041768 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 49292377) ^ 835464 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 49292377) ^ 9912 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_54491527 : Nat.Prime 54491527 := by
  apply lucas_primality 54491527 (6 : ZMod 54491527)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (57119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (57119, 1)] : List FactorBlock).map factorBlockValue).prod) = 54491527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_57119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 54491527) ^ 27245763 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 54491527) ^ 18163842 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 54491527) ^ 1028142 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 54491527) ^ 954 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_54582989 : Nat.Prime 54582989 := by
  apply lucas_primality 54582989 (2 : ZMod 54582989)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (29, 1), (89, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (29, 1), (89, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 54582989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_89
      · exact prime_eightyEightCH_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54582989) ^ 27291494 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54582989) ^ 3210764 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54582989) ^ 1882172 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54582989) ^ 613292 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 54582989) ^ 175508 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_55527737 : Nat.Prime 55527737 := by
  apply lucas_primality 55527737 (3 : ZMod 55527737)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (630997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (630997, 1)] : List FactorBlock).map factorBlockValue).prod) = 55527737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_630997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55527737) ^ 27763868 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55527737) ^ 5047976 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55527737) ^ 88 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_62774401 : Nat.Prime 62774401 := by
  apply lucas_primality 62774401 (11 : ZMod 62774401)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (13, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (13, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 62774401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 62774401) ^ 31387200 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 62774401) ^ 20924800 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 62774401) ^ 12554880 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 62774401) ^ 4828800 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 62774401) ^ 124800 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_64476833 : Nat.Prime 64476833 := by
  apply lucas_primality 64476833 (3 : ZMod 64476833)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (53, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (53, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) = 64476833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_5431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64476833) ^ 32238416 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64476833) ^ 9210976 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64476833) ^ 1216544 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64476833) ^ 11872 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_74041811 : Nat.Prime 74041811 := by
  apply lucas_primality 74041811 (6 : ZMod 74041811)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (83, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (83, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 74041811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_83
      · exact prime_eightyEightCH_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74041811) ^ 37020905 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 74041811) ^ 14808362 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 74041811) ^ 2001130 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 74041811) ^ 892070 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 74041811) ^ 30710 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_78460687 : Nat.Prime 78460687 := by
  apply lucas_primality 78460687 (3 : ZMod 78460687)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4358927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4358927, 1)] : List FactorBlock).map factorBlockValue).prod) = 78460687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_4358927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 78460687) ^ 39230343 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 78460687) ^ 26153562 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 78460687) ^ 18 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_91753933 : Nat.Prime 91753933 := by
  apply lucas_primality 91753933 (5 : ZMod 91753933)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (197, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (197, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 91753933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_197
      · exact prime_eightyEightCH_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 91753933) ^ 45876966 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 91753933) ^ 30584644 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 91753933) ^ 2479836 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 91753933) ^ 465756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 91753933) ^ 87468 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_95019097 : Nat.Prime 95019097 := by
  apply lucas_primality 95019097 (5 : ZMod 95019097)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3959129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3959129, 1)] : List FactorBlock).map factorBlockValue).prod) = 95019097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_3959129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 95019097) ^ 47509548 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 95019097) ^ 31673032 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 95019097) ^ 24 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_95613589 : Nat.Prime 95613589 := by
  apply lucas_primality 95613589 (10 : ZMod 95613589)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (126473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (126473, 1)] : List FactorBlock).map factorBlockValue).prod) = 95613589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_126473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 95613589) ^ 47806794 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 95613589) ^ 31871196 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 95613589) ^ 13659084 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 95613589) ^ 756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_102333859 : Nat.Prime 102333859 := by
  apply lucas_primality 102333859 (3 : ZMod 102333859)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1550513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1550513, 1)] : List FactorBlock).map factorBlockValue).prod) = 102333859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_1550513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102333859) ^ 51166929 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 102333859) ^ 34111286 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 102333859) ^ 9303078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 102333859) ^ 66 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_103239881 : Nat.Prime 103239881 := by
  apply lucas_primality 103239881 (3 : ZMod 103239881)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2580997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2580997, 1)] : List FactorBlock).map factorBlockValue).prod) = 103239881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_2580997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 103239881) ^ 51619940 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103239881) ^ 20647976 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103239881) ^ 40 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_106833707 : Nat.Prime 106833707 := by
  apply lucas_primality 106833707 (2 : ZMod 106833707)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7630979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7630979, 1)] : List FactorBlock).map factorBlockValue).prod) = 106833707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_7630979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 106833707) ^ 53416853 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 106833707) ^ 15261958 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 106833707) ^ 14 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_113503609 : Nat.Prime 113503609 := by
  apply lucas_primality 113503609 (11 : ZMod 113503609)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (449, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (449, 1), (3511, 1)] : List FactorBlock).map factorBlockValue).prod) = 113503609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_449
      · exact prime_eightyEightCH_3511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 113503609) ^ 56751804 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 113503609) ^ 37834536 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 113503609) ^ 252792 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 113503609) ^ 32328 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_114681547 : Nat.Prime 114681547 := by
  apply lucas_primality 114681547 (5 : ZMod 114681547)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (910171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (910171, 1)] : List FactorBlock).map factorBlockValue).prod) = 114681547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_910171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 114681547) ^ 57340773 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 114681547) ^ 38227182 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 114681547) ^ 16383078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 114681547) ^ 126 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_125564861 : Nat.Prime 125564861 := by
  apply lucas_primality 125564861 (10 : ZMod 125564861)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6278243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6278243, 1)] : List FactorBlock).map factorBlockValue).prod) = 125564861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_6278243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 125564861) ^ 62782430 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 125564861) ^ 25112972 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 125564861) ^ 20 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_127914257 : Nat.Prime 127914257 := by
  apply lucas_primality 127914257 (3 : ZMod 127914257)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (67, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (67, 1), (7019, 1)] : List FactorBlock).map factorBlockValue).prod) = 127914257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_67
      · exact prime_eightyEightCH_7019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 127914257) ^ 63957128 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127914257) ^ 7524368 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127914257) ^ 1909168 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127914257) ^ 18224 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_135586133 : Nat.Prime 135586133 := by
  apply lucas_primality 135586133 (2 : ZMod 135586133)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3081503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3081503, 1)] : List FactorBlock).map factorBlockValue).prod) = 135586133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_3081503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 135586133) ^ 67793066 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 135586133) ^ 12326012 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 135586133) ^ 44 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_144654131 : Nat.Prime 144654131 := by
  apply lucas_primality 144654131 (2 : ZMod 144654131)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (131, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (131, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) = 144654131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_131
      · exact prime_eightyEightCH_4801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144654131) ^ 72327065 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144654131) ^ 28930826 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144654131) ^ 6289310 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144654131) ^ 1104230 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144654131) ^ 30130 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_161871173 : Nat.Prime 161871173 := by
  apply lucas_primality 161871173 (2 : ZMod 161871173)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1117, 1), (36229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1117, 1), (36229, 1)] : List FactorBlock).map factorBlockValue).prod) = 161871173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1117
      · exact prime_eightyEightCH_36229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 161871173) ^ 80935586 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161871173) ^ 144916 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 161871173) ^ 4468 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_182617543 : Nat.Prime 182617543 := by
  apply lucas_primality 182617543 (5 : ZMod 182617543)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (107, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (107, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 182617543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_107
      · exact prime_eightyEightCH_1789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 182617543) ^ 91308771 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 182617543) ^ 60872514 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 182617543) ^ 3445614 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 182617543) ^ 1706706 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 182617543) ^ 102078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_185196931 : Nat.Prime 185196931 := by
  apply lucas_primality 185196931 (3 : ZMod 185196931)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (557, 1), (11083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (557, 1), (11083, 1)] : List FactorBlock).map factorBlockValue).prod) = 185196931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_557
      · exact prime_eightyEightCH_11083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185196931) ^ 92598465 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185196931) ^ 61732310 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185196931) ^ 37039386 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185196931) ^ 332490 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 185196931) ^ 16710 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_197953619 : Nat.Prime 197953619 := by
  apply lucas_primality 197953619 (2 : ZMod 197953619)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (277, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (277, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 197953619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_79
      · exact prime_eightyEightCH_277
      · exact prime_eightyEightCH_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 197953619) ^ 98976809 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 197953619) ^ 2505742 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 197953619) ^ 714634 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 197953619) ^ 43766 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_199233443 : Nat.Prime 199233443 := by
  apply lucas_primality 199233443 (2 : ZMod 199233443)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (61, 1), (89, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (61, 1), (89, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 199233443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_61
      · exact prime_eightyEightCH_89
      · exact prime_eightyEightCH_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 199233443) ^ 99616721 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 199233443) ^ 3376838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 199233443) ^ 3266122 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 199233443) ^ 2238578 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 199233443) ^ 640622 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_200416939 : Nat.Prime 200416939 := by
  apply lucas_primality 200416939 (3 : ZMod 200416939)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (41, 1), (97, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (41, 1), (97, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 200416939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_97
      · exact prime_eightyEightCH_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 200416939) ^ 100208469 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 200416939) ^ 66805646 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 200416939) ^ 5416674 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 200416939) ^ 4888218 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 200416939) ^ 2066154 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 200416939) ^ 882894 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_201093719 : Nat.Prime 201093719 := by
  apply lucas_primality 201093719 (13 : ZMod 201093719)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167, 1), (86011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167, 1), (86011, 1)] : List FactorBlock).map factorBlockValue).prod) = 201093719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_167
      · exact prime_eightyEightCH_86011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 201093719) ^ 100546859 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 201093719) ^ 28727674 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 201093719) ^ 1204154 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 201093719) ^ 2338 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_207029029 : Nat.Prime 207029029 := by
  apply lucas_primality 207029029 (2 : ZMod 207029029)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (594911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (594911, 1)] : List FactorBlock).map factorBlockValue).prod) = 207029029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_594911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 207029029) ^ 103514514 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 207029029) ^ 69009676 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 207029029) ^ 7138932 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 207029029) ^ 348 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_247674433 : Nat.Prime 247674433 := by
  apply lucas_primality 247674433 (11 : ZMod 247674433)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1289971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1289971, 1)] : List FactorBlock).map factorBlockValue).prod) = 247674433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1289971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 247674433) ^ 123837216 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 247674433) ^ 82558144 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 247674433) ^ 192 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_285102731 : Nat.Prime 285102731 := by
  apply lucas_primality 285102731 (6 : ZMod 285102731)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (2591843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (2591843, 1)] : List FactorBlock).map factorBlockValue).prod) = 285102731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_2591843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 285102731) ^ 142551365 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 285102731) ^ 57020546 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 285102731) ^ 25918430 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 285102731) ^ 110 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_314146013 : Nat.Prime 314146013 := by
  apply lucas_primality 314146013 (2 : ZMod 314146013)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2029, 1), (38707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2029, 1), (38707, 1)] : List FactorBlock).map factorBlockValue).prod) = 314146013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2029
      · exact prime_eightyEightCH_38707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 314146013) ^ 157073006 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 314146013) ^ 154828 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 314146013) ^ 8116 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_314341987 : Nat.Prime 314341987 := by
  apply lucas_primality 314341987 (2 : ZMod 314341987)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7484333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7484333, 1)] : List FactorBlock).map factorBlockValue).prod) = 314341987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_7484333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 314341987) ^ 157170993 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 314341987) ^ 104780662 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 314341987) ^ 44905998 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 314341987) ^ 42 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_332247997 : Nat.Prime 332247997 := by
  apply lucas_primality 332247997 (2 : ZMod 332247997)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (9229111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (9229111, 1)] : List FactorBlock).map factorBlockValue).prod) = 332247997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_9229111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 332247997) ^ 166123998 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 332247997) ^ 110749332 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 332247997) ^ 36 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_344851217 : Nat.Prime 344851217 := by
  apply lucas_primality 344851217 (3 : ZMod 344851217)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (139, 1), (8161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (139, 1), (8161, 1)] : List FactorBlock).map factorBlockValue).prod) = 344851217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_139
      · exact prime_eightyEightCH_8161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 344851217) ^ 172425608 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 344851217) ^ 18150064 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 344851217) ^ 2480944 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 344851217) ^ 42256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_349946573 : Nat.Prime 349946573 := by
  apply lucas_primality 349946573 (2 : ZMod 349946573)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2137, 1), (40939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2137, 1), (40939, 1)] : List FactorBlock).map factorBlockValue).prod) = 349946573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2137
      · exact prime_eightyEightCH_40939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 349946573) ^ 174973286 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 349946573) ^ 163756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 349946573) ^ 8548 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_361119877 : Nat.Prime 361119877 := by
  apply lucas_primality 361119877 (2 : ZMod 361119877)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (178067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (178067, 1)] : List FactorBlock).map factorBlockValue).prod) = 361119877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_178067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361119877) ^ 180559938 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 361119877) ^ 120373292 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 361119877) ^ 27778452 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 361119877) ^ 2028 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_367804433 : Nat.Prime 367804433 := by
  apply lucas_primality 367804433 (3 : ZMod 367804433)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (1209883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (1209883, 1)] : List FactorBlock).map factorBlockValue).prod) = 367804433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_1209883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 367804433) ^ 183902216 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 367804433) ^ 19358128 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 367804433) ^ 304 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_368737451 : Nat.Prime 368737451 := by
  apply lucas_primality 368737451 (2 : ZMod 368737451)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7374749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7374749, 1)] : List FactorBlock).map factorBlockValue).prod) = 368737451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7374749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 368737451) ^ 184368725 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368737451) ^ 73747490 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368737451) ^ 50 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_376253513 : Nat.Prime 376253513 := by
  apply lucas_primality 376253513 (3 : ZMod 376253513)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (211, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (211, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) = 376253513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_137
      · exact prime_eightyEightCH_211
      · exact prime_eightyEightCH_1627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 376253513) ^ 188126756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 376253513) ^ 2746376 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 376253513) ^ 1783192 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 376253513) ^ 231256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_378303749 : Nat.Prime 378303749 := by
  apply lucas_primality 378303749 (2 : ZMod 378303749)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1597, 1), (59221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1597, 1), (59221, 1)] : List FactorBlock).map factorBlockValue).prod) = 378303749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1597
      · exact prime_eightyEightCH_59221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 378303749) ^ 189151874 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 378303749) ^ 236884 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 378303749) ^ 6388 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_402187439 : Nat.Prime 402187439 := by
  apply lucas_primality 402187439 (11 : ZMod 402187439)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (201093719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (201093719, 1)] : List FactorBlock).map factorBlockValue).prod) = 402187439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_201093719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 402187439) ^ 201093719 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 402187439) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_467388379 : Nat.Prime 467388379 := by
  apply lucas_primality 467388379 (2 : ZMod 467388379)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (137, 1), (11149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (137, 1), (11149, 1)] : List FactorBlock).map factorBlockValue).prod) = 467388379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_137
      · exact prime_eightyEightCH_11149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 467388379) ^ 233694189 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 467388379) ^ 155796126 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 467388379) ^ 27493434 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 467388379) ^ 3411594 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 467388379) ^ 41922 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_568712867 : Nat.Prime 568712867 := by
  apply lucas_primality 568712867 (2 : ZMod 568712867)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (452077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (452077, 1)] : List FactorBlock).map factorBlockValue).prod) = 568712867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_452077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 568712867) ^ 284356433 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 568712867) ^ 33453698 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 568712867) ^ 15370618 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 568712867) ^ 1258 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_569943811 : Nat.Prime 569943811 := by
  apply lucas_primality 569943811 (3 : ZMod 569943811)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (317, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (317, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 569943811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 569943811) ^ 284971905 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 569943811) ^ 189981270 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 569943811) ^ 113988762 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 569943811) ^ 1797930 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 569943811) ^ 85590 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_570205463 : Nat.Prime 570205463 := by
  apply lucas_primality 570205463 (5 : ZMod 570205463)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (285102731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (285102731, 1)] : List FactorBlock).map factorBlockValue).prod) = 570205463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_285102731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 570205463) ^ 285102731 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 570205463) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_597343547 : Nat.Prime 597343547 := by
  apply lucas_primality 597343547 (2 : ZMod 597343547)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (15719567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (15719567, 1)] : List FactorBlock).map factorBlockValue).prod) = 597343547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_15719567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 597343547) ^ 298671773 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597343547) ^ 31439134 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597343547) ^ 38 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_603537953 : Nat.Prime 603537953 := by
  apply lucas_primality 603537953 (3 : ZMod 603537953)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (727, 1), (25943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (727, 1), (25943, 1)] : List FactorBlock).map factorBlockValue).prod) = 603537953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_727
      · exact prime_eightyEightCH_25943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 603537953) ^ 301768976 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 603537953) ^ 830176 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 603537953) ^ 23264 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_625404643 : Nat.Prime 625404643 := by
  apply lucas_primality 625404643 (2 : ZMod 625404643)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (127, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (127, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) = 625404643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_127
      · exact prime_eightyEightCH_19087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625404643) ^ 312702321 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625404643) ^ 208468214 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625404643) ^ 14544294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625404643) ^ 4924446 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625404643) ^ 32766 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_639213581 : Nat.Prime 639213581 := by
  apply lucas_primality 639213581 (2 : ZMod 639213581)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (1039, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (1039, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 639213581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_1039
      · exact prime_eightyEightCH_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 639213581) ^ 319606790 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 639213581) ^ 127842716 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 639213581) ^ 33642820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 639213581) ^ 615220 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 639213581) ^ 394820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_664960033 : Nat.Prime 664960033 := by
  apply lucas_primality 664960033 (7 : ZMod 664960033)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (17, 1), (12347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (17, 1), (12347, 1)] : List FactorBlock).map factorBlockValue).prod) = 664960033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_12347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 664960033) ^ 332480016 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 664960033) ^ 221653344 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 664960033) ^ 60450912 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 664960033) ^ 39115296 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 664960033) ^ 53856 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_671847929 : Nat.Prime 671847929 := by
  apply lucas_primality 671847929 (3 : ZMod 671847929)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (1584547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (1584547, 1)] : List FactorBlock).map factorBlockValue).prod) = 671847929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_1584547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 671847929) ^ 335923964 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 671847929) ^ 12676376 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 671847929) ^ 424 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_759752459 : Nat.Prime 759752459 := by
  apply lucas_primality 759752459 (2 : ZMod 759752459)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5741, 1), (66169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5741, 1), (66169, 1)] : List FactorBlock).map factorBlockValue).prod) = 759752459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5741
      · exact prime_eightyEightCH_66169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 759752459) ^ 379876229 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 759752459) ^ 132338 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 759752459) ^ 11482 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_889191529 : Nat.Prime 889191529 := by
  apply lucas_primality 889191529 (11 : ZMod 889191529)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (2179391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (2179391, 1)] : List FactorBlock).map factorBlockValue).prod) = 889191529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_2179391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 889191529) ^ 444595764 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 889191529) ^ 296397176 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 889191529) ^ 52305384 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 889191529) ^ 408 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_897914497 : Nat.Prime 897914497 := by
  apply lucas_primality 897914497 (5 : ZMod 897914497)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (229, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (229, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) = 897914497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_229
      · exact prime_eightyEightCH_10211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 897914497) ^ 448957248 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 897914497) ^ 299304832 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 897914497) ^ 3921024 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 897914497) ^ 87936 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_899406721 : Nat.Prime 899406721 := by
  apply lucas_primality 899406721 (17 : ZMod 899406721)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (23, 1), (31, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (23, 1), (31, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 899406721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 899406721) ^ 449703360 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 899406721) ^ 299802240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 899406721) ^ 179881344 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 899406721) ^ 39104640 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 899406721) ^ 29013120 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 899406721) ^ 12320640 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_924656599 : Nat.Prime 924656599 := by
  apply lucas_primality 924656599 (3 : ZMod 924656599)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (593, 1), (86627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (593, 1), (86627, 1)] : List FactorBlock).map factorBlockValue).prod) = 924656599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_593
      · exact prime_eightyEightCH_86627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 924656599) ^ 462328299 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 924656599) ^ 308218866 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 924656599) ^ 1559286 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 924656599) ^ 10674 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_948353689 : Nat.Prime 948353689 := by
  apply lucas_primality 948353689 (7 : ZMod 948353689)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (151, 1), (4591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (151, 1), (4591, 1)] : List FactorBlock).map factorBlockValue).prod) = 948353689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_4591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 948353689) ^ 474176844 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 948353689) ^ 316117896 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 948353689) ^ 49913352 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 948353689) ^ 6280488 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 948353689) ^ 206568 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_980338861 : Nat.Prime 980338861 := by
  apply lucas_primality 980338861 (6 : ZMod 980338861)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (5446327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (5446327, 1)] : List FactorBlock).map factorBlockValue).prod) = 980338861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_5446327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 980338861) ^ 490169430 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 980338861) ^ 326779620 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 980338861) ^ 196067772 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 980338861) ^ 180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1001280653 : Nat.Prime 1001280653 := by
  apply lucas_primality 1001280653 (2 : ZMod 1001280653)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8117, 1), (30839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8117, 1), (30839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1001280653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_8117
      · exact prime_eightyEightCH_30839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1001280653) ^ 500640326 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001280653) ^ 123356 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1001280653) ^ 32468 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1011078853 : Nat.Prime 1011078853 := by
  apply lucas_primality 1011078853 (2 : ZMod 1011078853)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (47, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (47, 1), (8831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1011078853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_47
      · exact prime_eightyEightCH_8831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1011078853) ^ 505539426 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011078853) ^ 337026284 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011078853) ^ 144439836 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011078853) ^ 34864788 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011078853) ^ 21512316 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011078853) ^ 114492 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1110328279 : Nat.Prime 1110328279 := by
  apply lucas_primality 1110328279 (3 : ZMod 1110328279)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (227, 1), (28111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (227, 1), (28111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110328279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_227
      · exact prime_eightyEightCH_28111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1110328279) ^ 555164139 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110328279) ^ 370109426 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110328279) ^ 38287182 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110328279) ^ 4891314 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110328279) ^ 39498 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1145972089 : Nat.Prime 1145972089 := by
  apply lucas_primality 1145972089 (13 : ZMod 1145972089)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1123, 1), (14173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1123, 1), (14173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145972089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1123
      · exact prime_eightyEightCH_14173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1145972089) ^ 572986044 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 1145972089) ^ 381990696 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 1145972089) ^ 1020456 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 1145972089) ^ 80856 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1232236769 : Nat.Prime 1232236769 := by
  apply lucas_primality 1232236769 (3 : ZMod 1232236769)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (5501057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (5501057, 1)] : List FactorBlock).map factorBlockValue).prod) = 1232236769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_5501057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1232236769) ^ 616118384 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1232236769) ^ 176033824 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1232236769) ^ 224 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1241115061 : Nat.Prime 1241115061 := by
  apply lucas_primality 1241115061 (6 : ZMod 1241115061)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (509, 1), (40639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (509, 1), (40639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1241115061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_509
      · exact prime_eightyEightCH_40639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1241115061) ^ 620557530 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1241115061) ^ 413705020 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1241115061) ^ 248223012 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1241115061) ^ 2438340 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1241115061) ^ 30540 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1329530539 : Nat.Prime 1329530539 := by
  apply lucas_primality 1329530539 (2 : ZMod 1329530539)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (151, 1), (209639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (151, 1), (209639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1329530539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_209639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1329530539) ^ 664765269 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329530539) ^ 443176846 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329530539) ^ 189932934 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329530539) ^ 8804838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1329530539) ^ 6342 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1361595167 : Nat.Prime 1361595167 := by
  apply lucas_primality 1361595167 (5 : ZMod 1361595167)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1447, 1), (470489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1447, 1), (470489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1361595167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1447
      · exact prime_eightyEightCH_470489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1361595167) ^ 680797583 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361595167) ^ 940978 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361595167) ^ 2894 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1519504919 : Nat.Prime 1519504919 := by
  apply lucas_primality 1519504919 (7 : ZMod 1519504919)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (759752459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (759752459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1519504919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_759752459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 1519504919) ^ 759752459 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1519504919) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1672983019 : Nat.Prime 1672983019 := by
  apply lucas_primality 1672983019 (2 : ZMod 1672983019)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (89, 1), (223, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (89, 1), (223, 2)] : List FactorBlock).map factorBlockValue).prod) = 1672983019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_89
      · exact prime_eightyEightCH_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1672983019) ^ 836491509 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672983019) ^ 557661006 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672983019) ^ 238997574 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672983019) ^ 18797562 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672983019) ^ 7502166 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1776980273 : Nat.Prime 1776980273 := by
  apply lucas_primality 1776980273 (3 : ZMod 1776980273)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (317, 1), (350351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (317, 1), (350351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1776980273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_350351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1776980273) ^ 888490136 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1776980273) ^ 5605616 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1776980273) ^ 5072 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1830231133 : Nat.Prime 1830231133 := by
  apply lucas_primality 1830231133 (22 : ZMod 1830231133)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (541, 1), (281921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (541, 1), (281921, 1)] : List FactorBlock).map factorBlockValue).prod) = 1830231133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_541
      · exact prime_eightyEightCH_281921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 1830231133) ^ 915115566 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (22 : ZMod 1830231133) ^ 610077044 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (22 : ZMod 1830231133) ^ 3383052 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (22 : ZMod 1830231133) ^ 6492 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1931469349 : Nat.Prime 1931469349 := by
  apply lucas_primality 1931469349 (2 : ZMod 1931469349)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (9467987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (9467987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1931469349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_9467987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1931469349) ^ 965734674 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931469349) ^ 643823116 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931469349) ^ 113615844 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1931469349) ^ 204 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2032121057 : Nat.Prime 2032121057 := by
  apply lucas_primality 2032121057 (3 : ZMod 2032121057)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (9071969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (9071969, 1)] : List FactorBlock).map factorBlockValue).prod) = 2032121057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_9071969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2032121057) ^ 1016060528 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032121057) ^ 290303008 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2032121057) ^ 224 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2081614957 : Nat.Prime 2081614957 := by
  apply lucas_primality 2081614957 (2 : ZMod 2081614957)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (271, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (271, 1), (6599, 1)] : List FactorBlock).map factorBlockValue).prod) = 2081614957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_97
      · exact prime_eightyEightCH_271
      · exact prime_eightyEightCH_6599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2081614957) ^ 1040807478 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2081614957) ^ 693871652 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2081614957) ^ 21459948 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2081614957) ^ 7681236 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2081614957) ^ 315444 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2093267023 : Nat.Prime 2093267023 := by
  apply lucas_primality 2093267023 (7 : ZMod 2093267023)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (317, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (317, 1), (14293, 1)] : List FactorBlock).map factorBlockValue).prod) = 2093267023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_14293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2093267023) ^ 1046633511 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2093267023) ^ 697755674 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2093267023) ^ 299038146 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2093267023) ^ 190297002 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2093267023) ^ 6603366 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2093267023) ^ 146454 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2166719263 : Nat.Prime 2166719263 := by
  apply lucas_primality 2166719263 (3 : ZMod 2166719263)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (361119877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (361119877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2166719263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_361119877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2166719263) ^ 1083359631 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2166719263) ^ 722239754 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2166719263) ^ 6 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2562816161 : Nat.Prime 2562816161 := by
  apply lucas_primality 2562816161 (3 : ZMod 2562816161)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (16017601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (16017601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2562816161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_16017601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2562816161) ^ 1281408080 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2562816161) ^ 512563232 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2562816161) ^ 160 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2661788359 : Nat.Prime 2661788359 := by
  apply lucas_primality 2661788359 (17 : ZMod 2661788359)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (49292377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (49292377, 1)] : List FactorBlock).map factorBlockValue).prod) = 2661788359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_49292377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 2661788359) ^ 1330894179 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2661788359) ^ 887262786 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2661788359) ^ 54 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2806067503 : Nat.Prime 2806067503 := by
  apply lucas_primality 2806067503 (3 : ZMod 2806067503)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2087, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2087, 1), (3557, 1)] : List FactorBlock).map factorBlockValue).prod) = 2806067503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_2087
      · exact prime_eightyEightCH_3557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2806067503) ^ 1403033751 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2806067503) ^ 935355834 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2806067503) ^ 400866786 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2806067503) ^ 1344546 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2806067503) ^ 788886 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2869672217 : Nat.Prime 2869672217 := by
  apply lucas_primality 2869672217 (5 : ZMod 2869672217)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (21100531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (21100531, 1)] : List FactorBlock).map factorBlockValue).prod) = 2869672217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_21100531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2869672217) ^ 1434836108 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2869672217) ^ 168804248 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2869672217) ^ 136 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2989646411 : Nat.Prime 2989646411 := by
  apply lucas_primality 2989646411 (2 : ZMod 2989646411)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3461, 1), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3461, 1), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) = 2989646411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_3461
      · exact prime_eightyEightCH_86381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2989646411) ^ 1494823205 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2989646411) ^ 597929282 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2989646411) ^ 863810 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2989646411) ^ 34610 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3053356919 : Nat.Prime 3053356919 := by
  apply lucas_primality 3053356919 (7 : ZMod 3053356919)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3767, 1), (405277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3767, 1), (405277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3053356919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3767
      · exact prime_eightyEightCH_405277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3053356919) ^ 1526678459 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3053356919) ^ 810554 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3053356919) ^ 7534 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3107626421 : Nat.Prime 3107626421 := by
  apply lucas_primality 3107626421 (2 : ZMod 3107626421)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5443, 1), (28547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5443, 1), (28547, 1)] : List FactorBlock).map factorBlockValue).prod) = 3107626421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_5443
      · exact prime_eightyEightCH_28547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3107626421) ^ 1553813210 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3107626421) ^ 621525284 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3107626421) ^ 570940 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3107626421) ^ 108860 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3274239061 : Nat.Prime 3274239061 := by
  apply lucas_primality 3274239061 (6 : ZMod 3274239061)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (23, 1), (790879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (23, 1), (790879, 1)] : List FactorBlock).map factorBlockValue).prod) = 3274239061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_790879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3274239061) ^ 1637119530 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3274239061) ^ 1091413020 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3274239061) ^ 654847812 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3274239061) ^ 142358220 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 3274239061) ^ 4140 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4350620387 : Nat.Prime 4350620387 := by
  apply lucas_primality 4350620387 (2 : ZMod 4350620387)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (199, 1), (1561601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (199, 1), (1561601, 1)] : List FactorBlock).map factorBlockValue).prod) = 4350620387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_199
      · exact prime_eightyEightCH_1561601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4350620387) ^ 2175310193 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4350620387) ^ 621517198 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4350620387) ^ 21862414 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4350620387) ^ 2786 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4424849413 : Nat.Prime 4424849413 := by
  apply lucas_primality 4424849413 (11 : ZMod 4424849413)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (368737451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (368737451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4424849413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_368737451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4424849413) ^ 2212424706 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4424849413) ^ 1474949804 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 4424849413) ^ 12 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_5015965247 : Nat.Prime 5015965247 := by
  apply lucas_primality 5015965247 (5 : ZMod 5015965247)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17657, 1), (142039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17657, 1), (142039, 1)] : List FactorBlock).map factorBlockValue).prod) = 5015965247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17657
      · exact prime_eightyEightCH_142039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5015965247) ^ 2507982623 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5015965247) ^ 284078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5015965247) ^ 35314 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_5204063983 : Nat.Prime 5204063983 := by
  apply lucas_primality 5204063983 (5 : ZMod 5204063983)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (5132213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (5132213, 1)] : List FactorBlock).map factorBlockValue).prod) = 5204063983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_5132213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5204063983) ^ 2602031991 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5204063983) ^ 1734687994 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5204063983) ^ 400312614 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5204063983) ^ 1014 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6691932077 : Nat.Prime 6691932077 := by
  apply lucas_primality 6691932077 (2 : ZMod 6691932077)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1672983019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1672983019, 1)] : List FactorBlock).map factorBlockValue).prod) = 6691932077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1672983019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6691932077) ^ 3345966038 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6691932077) ^ 4 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6973298909 : Nat.Prime 6973298909 := by
  apply lucas_primality 6973298909 (2 : ZMod 6973298909)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (91753933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (91753933, 1)] : List FactorBlock).map factorBlockValue).prod) = 6973298909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_91753933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6973298909) ^ 3486649454 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6973298909) ^ 367015732 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6973298909) ^ 76 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_9322636459 : Nat.Prime 9322636459 := by
  apply lucas_primality 9322636459 (2 : ZMod 9322636459)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (1091, 1), (4639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (1091, 1), (4639, 1)] : List FactorBlock).map factorBlockValue).prod) = 9322636459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_307
      · exact prime_eightyEightCH_1091
      · exact prime_eightyEightCH_4639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9322636459) ^ 4661318229 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9322636459) ^ 3107545486 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9322636459) ^ 30366894 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9322636459) ^ 8545038 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9322636459) ^ 2009622 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_9861347323 : Nat.Prime 9861347323 := by
  apply lucas_primality 9861347323 (2 : ZMod 9861347323)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (182617543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (182617543, 1)] : List FactorBlock).map factorBlockValue).prod) = 9861347323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_182617543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9861347323) ^ 4930673661 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9861347323) ^ 3287115774 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9861347323) ^ 54 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_10780065419 : Nat.Prime 10780065419 := by
  apply lucas_primality 10780065419 (2 : ZMod 10780065419)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (114681547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (114681547, 1)] : List FactorBlock).map factorBlockValue).prod) = 10780065419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_47
      · exact prime_eightyEightCH_114681547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10780065419) ^ 5390032709 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10780065419) ^ 229363094 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10780065419) ^ 94 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_11506033733 : Nat.Prime 11506033733 := by
  apply lucas_primality 11506033733 (2 : ZMod 11506033733)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163, 1), (1543, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163, 1), (1543, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) = 11506033733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_163
      · exact prime_eightyEightCH_1543
      · exact prime_eightyEightCH_11437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11506033733) ^ 5753016866 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11506033733) ^ 70589164 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11506033733) ^ 7456924 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11506033733) ^ 1006036 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_12860606657 : Nat.Prime 12860606657 := by
  apply lucas_primality 12860606657 (3 : ZMod 12860606657)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (59, 1), (3405881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (59, 1), (3405881, 1)] : List FactorBlock).map factorBlockValue).prod) = 12860606657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_3405881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12860606657) ^ 6430303328 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12860606657) ^ 217976384 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12860606657) ^ 3776 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_13453291157 : Nat.Prime 13453291157 := by
  apply lucas_primality 13453291157 (2 : ZMod 13453291157)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (59, 1), (1499, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (59, 1), (1499, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) = 13453291157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_1499
      · exact prime_eightyEightCH_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13453291157) ^ 6726645578 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13453291157) ^ 791370068 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13453291157) ^ 228021884 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13453291157) ^ 8974844 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13453291157) ^ 6013988 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_14795394697 : Nat.Prime 14795394697 := by
  apply lucas_primality 14795394697 (5 : ZMod 14795394697)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (29, 1), (372943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (29, 1), (372943, 1)] : List FactorBlock).map factorBlockValue).prod) = 14795394697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_372943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14795394697) ^ 7397697348 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14795394697) ^ 4931798232 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14795394697) ^ 778704984 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14795394697) ^ 510186024 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14795394697) ^ 39672 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_15766513613 : Nat.Prime 15766513613 := by
  apply lucas_primality 15766513613 (2 : ZMod 15766513613)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (317, 1), (175129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (317, 1), (175129, 1)] : List FactorBlock).map factorBlockValue).prod) = 15766513613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_71
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_175129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15766513613) ^ 7883256806 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15766513613) ^ 222063572 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15766513613) ^ 49736636 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15766513613) ^ 90028 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_16070105801 : Nat.Prime 16070105801 := by
  apply lucas_primality 16070105801 (3 : ZMod 16070105801)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (41, 1), (279967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (41, 1), (279967, 1)] : List FactorBlock).map factorBlockValue).prod) = 16070105801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_279967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16070105801) ^ 8035052900 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16070105801) ^ 3214021160 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16070105801) ^ 2295729400 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16070105801) ^ 391953800 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16070105801) ^ 57400 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_16817127623 : Nat.Prime 16817127623 := by
  apply lucas_primality 16817127623 (5 : ZMod 16817127623)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (3089, 1), (57917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (3089, 1), (57917, 1)] : List FactorBlock).map factorBlockValue).prod) = 16817127623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_47
      · exact prime_eightyEightCH_3089
      · exact prime_eightyEightCH_57917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16817127623) ^ 8408563811 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16817127623) ^ 357811226 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16817127623) ^ 5444198 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 16817127623) ^ 290366 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_21625639001 : Nat.Prime 21625639001 := by
  apply lucas_primality 21625639001 (3 : ZMod 21625639001)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (7, 1), (3089377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (7, 1), (3089377, 1)] : List FactorBlock).map factorBlockValue).prod) = 21625639001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_3089377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21625639001) ^ 10812819500 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21625639001) ^ 4325127800 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21625639001) ^ 3089377000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21625639001) ^ 7000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_21629007019 : Nat.Prime 21629007019 := by
  apply lucas_primality 21629007019 (2 : ZMod 21629007019)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (83, 1), (1608583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (83, 1), (1608583, 1)] : List FactorBlock).map factorBlockValue).prod) = 21629007019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_83
      · exact prime_eightyEightCH_1608583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21629007019) ^ 10814503509 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21629007019) ^ 7209669006 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21629007019) ^ 260590446 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 21629007019) ^ 13446 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_23024566261 : Nat.Prime 23024566261 := by
  apply lucas_primality 23024566261 (2 : ZMod 23024566261)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (127914257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (127914257, 1)] : List FactorBlock).map factorBlockValue).prod) = 23024566261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_127914257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23024566261) ^ 11512283130 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23024566261) ^ 7674855420 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23024566261) ^ 4604913252 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23024566261) ^ 180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_23477448899 : Nat.Prime 23477448899 := by
  apply lucas_primality 23477448899 (2 : ZMod 23477448899)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (19997827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (19997827, 1)] : List FactorBlock).map factorBlockValue).prod) = 23477448899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_587
      · exact prime_eightyEightCH_19997827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23477448899) ^ 11738724449 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23477448899) ^ 39995654 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23477448899) ^ 1174 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_24508713007 : Nat.Prime 24508713007 := by
  apply lucas_primality 24508713007 (5 : ZMod 24508713007)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1361595167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1361595167, 1)] : List FactorBlock).map factorBlockValue).prod) = 24508713007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1361595167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 24508713007) ^ 12254356503 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 24508713007) ^ 8169571002 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 24508713007) ^ 18 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_25067461151 : Nat.Prime 25067461151 := by
  apply lucas_primality 25067461151 (13 : ZMod 25067461151)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (37, 1), (599, 1), (22621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (37, 1), (599, 1), (22621, 1)] : List FactorBlock).map factorBlockValue).prod) = 25067461151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_599
      · exact prime_eightyEightCH_22621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 25067461151) ^ 12533730575 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 25067461151) ^ 5013492230 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 25067461151) ^ 677498950 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 25067461151) ^ 41848850 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 25067461151) ^ 1108150 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_27852751613 : Nat.Prime 27852751613 := by
  apply lucas_primality 27852751613 (2 : ZMod 27852751613)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (139, 1), (7156411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (139, 1), (7156411, 1)] : List FactorBlock).map factorBlockValue).prod) = 27852751613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_139
      · exact prime_eightyEightCH_7156411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27852751613) ^ 13926375806 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27852751613) ^ 3978964516 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27852751613) ^ 200379508 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 27852751613) ^ 3892 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_28449694799 : Nat.Prime 28449694799 := by
  apply lucas_primality 28449694799 (7 : ZMod 28449694799)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2032121057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2032121057, 1)] : List FactorBlock).map factorBlockValue).prod) = 28449694799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_2032121057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 28449694799) ^ 14224847399 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28449694799) ^ 4064242114 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28449694799) ^ 14 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_32026791497 : Nat.Prime 32026791497 := by
  apply lucas_primality 32026791497 (3 : ZMod 32026791497)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41, 1), (79, 1), (317, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41, 1), (79, 1), (317, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 32026791497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_79
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32026791497) ^ 16013395748 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 32026791497) ^ 4575255928 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 32026791497) ^ 781141256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 32026791497) ^ 405402424 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 32026791497) ^ 101030888 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 32026791497) ^ 57498728 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_43251278003 : Nat.Prime 43251278003 := by
  apply lucas_primality 43251278003 (2 : ZMod 43251278003)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21625639001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21625639001, 1)] : List FactorBlock).map factorBlockValue).prod) = 43251278003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_21625639001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 43251278003) ^ 21625639001 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43251278003) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_50105327719 : Nat.Prime 50105327719 := by
  apply lucas_primality 50105327719 (3 : ZMod 50105327719)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1559, 1), (5356567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1559, 1), (5356567, 1)] : List FactorBlock).map factorBlockValue).prod) = 50105327719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1559
      · exact prime_eightyEightCH_5356567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50105327719) ^ 25052663859 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50105327719) ^ 16701775906 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50105327719) ^ 32139402 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50105327719) ^ 9354 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_50881791161 : Nat.Prime 50881791161 := by
  apply lucas_primality 50881791161 (3 : ZMod 50881791161)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (59, 1), (269, 1), (80149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (59, 1), (269, 1), (80149, 1)] : List FactorBlock).map factorBlockValue).prod) = 50881791161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_269
      · exact prime_eightyEightCH_80149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50881791161) ^ 25440895580 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50881791161) ^ 10176358232 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50881791161) ^ 862403240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50881791161) ^ 189151640 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50881791161) ^ 634840 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_51302221543 : Nat.Prime 51302221543 := by
  apply lucas_primality 51302221543 (3 : ZMod 51302221543)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (13, 1), (1811903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (13, 1), (1811903, 1)] : List FactorBlock).map factorBlockValue).prod) = 51302221543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_1811903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51302221543) ^ 25651110771 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 51302221543) ^ 17100740514 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 51302221543) ^ 4663838322 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 51302221543) ^ 3946324734 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 51302221543) ^ 28314 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_53773265773 : Nat.Prime 53773265773 := by
  apply lucas_primality 53773265773 (2 : ZMod 53773265773)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (101, 2), (48809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (101, 2), (48809, 1)] : List FactorBlock).map factorBlockValue).prod) = 53773265773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_101
      · exact prime_eightyEightCH_48809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53773265773) ^ 26886632886 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53773265773) ^ 17924421924 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53773265773) ^ 532408572 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 53773265773) ^ 1101708 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_63613288829 : Nat.Prime 63613288829 := by
  apply lucas_primality 63613288829 (2 : ZMod 63613288829)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4219, 1), (3769453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4219, 1), (3769453, 1)] : List FactorBlock).map factorBlockValue).prod) = 63613288829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_4219
      · exact prime_eightyEightCH_3769453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63613288829) ^ 31806644414 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 63613288829) ^ 15077812 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 63613288829) ^ 16876 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_81299079319 : Nat.Prime 81299079319 := by
  apply lucas_primality 81299079319 (3 : ZMod 81299079319)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (743, 1), (492883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (743, 1), (492883, 1)] : List FactorBlock).map factorBlockValue).prod) = 81299079319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_743
      · exact prime_eightyEightCH_492883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81299079319) ^ 40649539659 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 81299079319) ^ 27099693106 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 81299079319) ^ 2197272414 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 81299079319) ^ 109420026 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 81299079319) ^ 164946 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_82242836993 : Nat.Prime 82242836993 := by
  apply lucas_primality 82242836993 (3 : ZMod 82242836993)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (19, 1), (8454239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (19, 1), (8454239, 1)] : List FactorBlock).map factorBlockValue).prod) = 82242836993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_8454239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 82242836993) ^ 41121418496 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82242836993) ^ 4328570368 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82242836993) ^ 9728 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_82630661077 : Nat.Prime 82630661077 := by
  apply lucas_primality 82630661077 (2 : ZMod 82630661077)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (74041811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (74041811, 1)] : List FactorBlock).map factorBlockValue).prod) = 82630661077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_74041811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82630661077) ^ 41315330538 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630661077) ^ 27543553692 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630661077) ^ 2665505196 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82630661077) ^ 1116 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_85712856899 : Nat.Prime 85712856899 := by
  apply lucas_primality 85712856899 (2 : ZMod 85712856899)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1009, 1), (1543, 1), (27527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1009, 1), (1543, 1), (27527, 1)] : List FactorBlock).map factorBlockValue).prod) = 85712856899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1009
      · exact prime_eightyEightCH_1543
      · exact prime_eightyEightCH_27527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85712856899) ^ 42856428449 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85712856899) ^ 84948322 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85712856899) ^ 55549486 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85712856899) ^ 3113774 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_89068691917 : Nat.Prime 89068691917 := by
  apply lucas_primality 89068691917 (2 : ZMod 89068691917)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 2), (2941891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 2), (2941891, 1)] : List FactorBlock).map factorBlockValue).prod) = 89068691917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_2941891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89068691917) ^ 44534345958 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 89068691917) ^ 29689563972 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 89068691917) ^ 3071334204 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 89068691917) ^ 30276 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_96732076279 : Nat.Prime 96732076279 := by
  apply lucas_primality 96732076279 (11 : ZMod 96732076279)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (948353689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (948353689, 1)] : List FactorBlock).map factorBlockValue).prod) = 96732076279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_948353689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 96732076279) ^ 48366038139 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 96732076279) ^ 32244025426 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 96732076279) ^ 5690122134 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 96732076279) ^ 102 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_101882083111 : Nat.Prime 101882083111 := by
  apply lucas_primality 101882083111 (6 : ZMod 101882083111)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (43, 1), (2547689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (43, 1), (2547689, 1)] : List FactorBlock).map factorBlockValue).prod) = 101882083111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_2547689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 101882083111) ^ 50941041555 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 101882083111) ^ 33960694370 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 101882083111) ^ 20376416622 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 101882083111) ^ 3286518810 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 101882083111) ^ 2369350770 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 101882083111) ^ 39990 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_106196385913 : Nat.Prime 106196385913 := by
  apply lucas_primality 106196385913 (10 : ZMod 106196385913)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4424849413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4424849413, 1)] : List FactorBlock).map factorBlockValue).prod) = 106196385913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_4424849413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 106196385913) ^ 53098192956 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 106196385913) ^ 35398795304 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 106196385913) ^ 24 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_108685780601 : Nat.Prime 108685780601 := by
  apply lucas_primality 108685780601 (3 : ZMod 108685780601)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (523, 1), (641, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (523, 1), (641, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 108685780601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_523
      · exact prime_eightyEightCH_641
      · exact prime_eightyEightCH_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 108685780601) ^ 54342890300 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 108685780601) ^ 21737156120 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 108685780601) ^ 207812200 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 108685780601) ^ 169556600 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 108685780601) ^ 67048600 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_147896488757 : Nat.Prime 147896488757 := by
  apply lucas_primality 147896488757 (2 : ZMod 147896488757)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (31, 1), (62774401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (31, 1), (62774401, 1)] : List FactorBlock).map factorBlockValue).prod) = 147896488757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_62774401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 147896488757) ^ 73948244378 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147896488757) ^ 7784025724 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147896488757) ^ 4770854476 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147896488757) ^ 2356 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_172274992199 : Nat.Prime 172274992199 := by
  apply lucas_primality 172274992199 (7 : ZMod 172274992199)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (59, 1), (35608721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (59, 1), (35608721, 1)] : List FactorBlock).map factorBlockValue).prod) = 172274992199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_35608721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 172274992199) ^ 86137496099 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 172274992199) ^ 4201829078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 172274992199) ^ 2919915122 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 172274992199) ^ 4838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_193841608889 : Nat.Prime 193841608889 := by
  apply lucas_primality 193841608889 (3 : ZMod 193841608889)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1889, 1), (12826999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1889, 1), (12826999, 1)] : List FactorBlock).map factorBlockValue).prod) = 193841608889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1889
      · exact prime_eightyEightCH_12826999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 193841608889) ^ 96920804444 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 193841608889) ^ 102615992 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 193841608889) ^ 15112 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_201331425389 : Nat.Prime 201331425389 := by
  apply lucas_primality 201331425389 (2 : ZMod 201331425389)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4889, 1), (10295123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4889, 1), (10295123, 1)] : List FactorBlock).map factorBlockValue).prod) = 201331425389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_4889
      · exact prime_eightyEightCH_10295123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 201331425389) ^ 100665712694 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 201331425389) ^ 41180492 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 201331425389) ^ 19556 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_204747703007 : Nat.Prime 204747703007 := by
  apply lucas_primality 204747703007 (5 : ZMod 204747703007)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1329530539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1329530539, 1)] : List FactorBlock).map factorBlockValue).prod) = 204747703007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_1329530539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 204747703007) ^ 102373851503 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 204747703007) ^ 29249671858 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 204747703007) ^ 18613427546 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 204747703007) ^ 154 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_223145565089 : Nat.Prime 223145565089 := by
  apply lucas_primality 223145565089 (3 : ZMod 223145565089)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6973298909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6973298909, 1)] : List FactorBlock).map factorBlockValue).prod) = 223145565089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_6973298909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 223145565089) ^ 111572782544 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 223145565089) ^ 32 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_299485297499 : Nat.Prime 299485297499 := by
  apply lucas_primality 299485297499 (2 : ZMod 299485297499)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (21599, 1), (64793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (21599, 1), (64793, 1)] : List FactorBlock).map factorBlockValue).prod) = 299485297499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_107
      · exact prime_eightyEightCH_21599
      · exact prime_eightyEightCH_64793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 299485297499) ^ 149742648749 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 299485297499) ^ 2798928014 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 299485297499) ^ 13865702 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 299485297499) ^ 4622186 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_304377459143 : Nat.Prime 304377459143 := by
  apply lucas_primality 304377459143 (5 : ZMod 304377459143)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (823, 1), (687433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (823, 1), (687433, 1)] : List FactorBlock).map factorBlockValue).prod) = 304377459143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_269
      · exact prime_eightyEightCH_823
      · exact prime_eightyEightCH_687433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 304377459143) ^ 152188729571 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 304377459143) ^ 1131514718 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 304377459143) ^ 369838954 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 304377459143) ^ 442774 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_489213176581 : Nat.Prime 489213176581 := by
  apply lucas_primality 489213176581 (2 : ZMod 489213176581)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (911, 1), (994457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (911, 1), (994457, 1)] : List FactorBlock).map factorBlockValue).prod) = 489213176581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_911
      · exact prime_eightyEightCH_994457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 489213176581) ^ 244606588290 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 489213176581) ^ 163071058860 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 489213176581) ^ 97842635316 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 489213176581) ^ 537006780 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 489213176581) ^ 491940 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_507448659539 : Nat.Prime 507448659539 := by
  apply lucas_primality 507448659539 (2 : ZMod 507448659539)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (193, 1), (42407543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (193, 1), (42407543, 1)] : List FactorBlock).map factorBlockValue).prod) = 507448659539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_193
      · exact prime_eightyEightCH_42407543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 507448659539) ^ 253724329769 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 507448659539) ^ 16369311598 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 507448659539) ^ 2629267666 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 507448659539) ^ 11966 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_605612196533 : Nat.Prime 605612196533 := by
  apply lucas_primality 605612196533 (2 : ZMod 605612196533)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (21629007019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (21629007019, 1)] : List FactorBlock).map factorBlockValue).prod) = 605612196533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_21629007019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 605612196533) ^ 302806098266 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 605612196533) ^ 86516028076 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 605612196533) ^ 28 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_753169807301 : Nat.Prime 753169807301 := by
  apply lucas_primality 753169807301 (14 : ZMod 753169807301)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (41, 1), (881, 1), (208513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (41, 1), (881, 1), (208513, 1)] : List FactorBlock).map factorBlockValue).prod) = 753169807301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_881
      · exact prime_eightyEightCH_208513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 753169807301) ^ 376584903650 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 753169807301) ^ 150633961460 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 753169807301) ^ 18369995300 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 753169807301) ^ 854903300 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 753169807301) ^ 3612100 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_813116919269 : Nat.Prime 813116919269 := by
  apply lucas_primality 813116919269 (2 : ZMod 813116919269)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (5869, 1), (232457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (5869, 1), (232457, 1)] : List FactorBlock).map factorBlockValue).prod) = 813116919269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_149
      · exact prime_eightyEightCH_5869
      · exact prime_eightyEightCH_232457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 813116919269) ^ 406558459634 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 813116919269) ^ 5457160532 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 813116919269) ^ 138544372 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 813116919269) ^ 3497924 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1152335239513 : Nat.Prime 1152335239513 := by
  apply lucas_primality 1152335239513 (5 : ZMod 1152335239513)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7451, 1), (6443963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7451, 1), (6443963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152335239513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7451
      · exact prime_eightyEightCH_6443963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1152335239513) ^ 576167619756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1152335239513) ^ 384111746504 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1152335239513) ^ 154655112 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1152335239513) ^ 178824 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1197241467133 : Nat.Prime 1197241467133 := by
  apply lucas_primality 1197241467133 (2 : ZMod 1197241467133)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (599, 1), (619, 1), (5077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (599, 1), (619, 1), (5077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1197241467133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_599
      · exact prime_eightyEightCH_619
      · exact prime_eightyEightCH_5077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1197241467133) ^ 598620733566 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197241467133) ^ 399080489044 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197241467133) ^ 22589461644 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197241467133) ^ 1998733668 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197241467133) ^ 1934154228 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197241467133) ^ 235816716 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1229663069839 : Nat.Prime 1229663069839 := by
  apply lucas_primality 1229663069839 (3 : ZMod 1229663069839)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (2393, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (2393, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod) = 1229663069839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_2393
      · exact prime_eightyEightCH_140629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1229663069839) ^ 614831534919 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229663069839) ^ 409887689946 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229663069839) ^ 175666152834 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229663069839) ^ 42402174822 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229663069839) ^ 513858366 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1229663069839) ^ 8744022 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1370451028883 : Nat.Prime 1370451028883 := by
  apply lucas_primality 1370451028883 (2 : ZMod 1370451028883)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (263, 1), (200416939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (263, 1), (200416939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370451028883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_263
      · exact prime_eightyEightCH_200416939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1370451028883) ^ 685225514441 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1370451028883) ^ 105419309914 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1370451028883) ^ 5210840414 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1370451028883) ^ 6838 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1602609644263 : Nat.Prime 1602609644263 := by
  apply lucas_primality 1602609644263 (3 : ZMod 1602609644263)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (58573, 1), (414559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (58573, 1), (414559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1602609644263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_58573
      · exact prime_eightyEightCH_414559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1602609644263) ^ 801304822131 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602609644263) ^ 534203214754 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602609644263) ^ 145691785842 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602609644263) ^ 27360894 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602609644263) ^ 3865818 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1637981624057 : Nat.Prime 1637981624057 := by
  apply lucas_primality 1637981624057 (3 : ZMod 1637981624057)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (204747703007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (204747703007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1637981624057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_204747703007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1637981624057) ^ 818990812028 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1637981624057) ^ 8 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1908398664871 : Nat.Prime 1908398664871 := by
  apply lucas_primality 1908398664871 (12 : ZMod 1908398664871)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (63613288829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (63613288829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908398664871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_63613288829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 1908398664871) ^ 954199332435 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1908398664871) ^ 636132888290 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1908398664871) ^ 381679732974 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (12 : ZMod 1908398664871) ^ 30 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2158399534223 : Nat.Prime 2158399534223 := by
  apply lucas_primality 2158399534223 (5 : ZMod 2158399534223)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2309, 1), (467388379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2309, 1), (467388379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2158399534223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2309
      · exact prime_eightyEightCH_467388379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2158399534223) ^ 1079199767111 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158399534223) ^ 934776758 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158399534223) ^ 4618 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2493890661001 : Nat.Prime 2493890661001 := by
  apply lucas_primality 2493890661001 (7 : ZMod 2493890661001)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (97, 1), (269, 1), (31859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (97, 1), (269, 1), (31859, 1)] : List FactorBlock).map factorBlockValue).prod) = 2493890661001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_97
      · exact prime_eightyEightCH_269
      · exact prime_eightyEightCH_31859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2493890661001) ^ 1246945330500 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2493890661001) ^ 831296887000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2493890661001) ^ 498778132200 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2493890661001) ^ 25710213000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2493890661001) ^ 9270969000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2493890661001) ^ 78279000 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2874412023229 : Nat.Prime 2874412023229 := by
  apply lucas_primality 2874412023229 (2 : ZMod 2874412023229)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (809, 1), (1153, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (809, 1), (1153, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) = 2874412023229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_809
      · exact prime_eightyEightCH_1153
      · exact prime_eightyEightCH_9511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2874412023229) ^ 1437206011614 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874412023229) ^ 958137341076 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874412023229) ^ 3553043292 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874412023229) ^ 2492985276 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2874412023229) ^ 302219748 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2956787581421 : Nat.Prime 2956787581421 := by
  apply lucas_primality 2956787581421 (2 : ZMod 2956787581421)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (523, 1), (16627981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (523, 1), (16627981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2956787581421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_523
      · exact prime_eightyEightCH_16627981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2956787581421) ^ 1478393790710 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956787581421) ^ 591357516284 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956787581421) ^ 173928681260 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956787581421) ^ 5653513540 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2956787581421) ^ 177820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3904899144253 : Nat.Prime 3904899144253 := by
  apply lucas_primality 3904899144253 (5 : ZMod 3904899144253)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (54361, 1), (127363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (54361, 1), (127363, 1)] : List FactorBlock).map factorBlockValue).prod) = 3904899144253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_47
      · exact prime_eightyEightCH_54361
      · exact prime_eightyEightCH_127363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3904899144253) ^ 1952449572126 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904899144253) ^ 1301633048084 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904899144253) ^ 83082960516 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904899144253) ^ 71832732 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3904899144253) ^ 30659604 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4382126289511 : Nat.Prime 4382126289511 := by
  apply lucas_primality 4382126289511 (3 : ZMod 4382126289511)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4349, 1), (33587233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4349, 1), (33587233, 1)] : List FactorBlock).map factorBlockValue).prod) = 4382126289511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_4349
      · exact prime_eightyEightCH_33587233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4382126289511) ^ 2191063144755 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382126289511) ^ 1460708763170 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382126289511) ^ 876425257902 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382126289511) ^ 1007616990 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382126289511) ^ 130470 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4426914739417 : Nat.Prime 4426914739417 := by
  apply lucas_primality 4426914739417 (15 : ZMod 4426914739417)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (113, 1), (125564861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (113, 1), (125564861, 1)] : List FactorBlock).map factorBlockValue).prod) = 4426914739417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_113
      · exact prime_eightyEightCH_125564861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 4426914739417) ^ 2213457369708 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 4426914739417) ^ 1475638246472 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 4426914739417) ^ 340531903032 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 4426914739417) ^ 39176236632 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 4426914739417) ^ 35256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6025358458409 : Nat.Prime 6025358458409 := by
  apply lucas_primality 6025358458409 (3 : ZMod 6025358458409)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (753169807301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (753169807301, 1)] : List FactorBlock).map factorBlockValue).prod) = 6025358458409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_753169807301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6025358458409) ^ 3012679229204 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6025358458409) ^ 8 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6076274325917 : Nat.Prime 6076274325917 := by
  apply lucas_primality 6076274325917 (2 : ZMod 6076274325917)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (227, 1), (6691932077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (227, 1), (6691932077, 1)] : List FactorBlock).map factorBlockValue).prod) = 6076274325917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_227
      · exact prime_eightyEightCH_6691932077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6076274325917) ^ 3038137162958 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6076274325917) ^ 26767728308 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6076274325917) ^ 908 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_7569253555169 : Nat.Prime 7569253555169 := by
  apply lucas_primality 7569253555169 (3 : ZMod 7569253555169)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (113, 1), (2093267023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (113, 1), (2093267023, 1)] : List FactorBlock).map factorBlockValue).prod) = 7569253555169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_113
      · exact prime_eightyEightCH_2093267023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7569253555169) ^ 3784626777584 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7569253555169) ^ 66984544736 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7569253555169) ^ 3616 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_13092682233977 : Nat.Prime 13092682233977 := by
  apply lucas_primality 13092682233977 (3 : ZMod 13092682233977)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (8837, 1), (185196931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (8837, 1), (185196931, 1)] : List FactorBlock).map factorBlockValue).prod) = 13092682233977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_8837
      · exact prime_eightyEightCH_185196931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13092682233977) ^ 6546341116988 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092682233977) ^ 1481575448 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092682233977) ^ 70696 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_13768621054723 : Nat.Prime 13768621054723 := by
  apply lucas_primality 13768621054723 (3 : ZMod 13768621054723)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (107, 1), (376253513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (107, 1), (376253513, 1)] : List FactorBlock).map factorBlockValue).prod) = 13768621054723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_107
      · exact prime_eightyEightCH_376253513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13768621054723) ^ 6884310527361 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13768621054723) ^ 4589540351574 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13768621054723) ^ 724664266038 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13768621054723) ^ 128678701446 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13768621054723) ^ 36594 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_17946589526069 : Nat.Prime 17946589526069 := by
  apply lucas_primality 17946589526069 (2 : ZMod 17946589526069)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (37, 1), (597343547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (37, 1), (597343547, 1)] : List FactorBlock).map factorBlockValue).prod) = 17946589526069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_597343547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17946589526069) ^ 8973294763034 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17946589526069) ^ 2563798503724 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17946589526069) ^ 618847914692 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17946589526069) ^ 485042960164 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 17946589526069) ^ 30044 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_19196603942093 : Nat.Prime 19196603942093 := by
  apply lucas_primality 19196603942093 (2 : ZMod 19196603942093)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (2039, 1), (102333859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (2039, 1), (102333859, 1)] : List FactorBlock).map factorBlockValue).prod) = 19196603942093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_2039
      · exact prime_eightyEightCH_102333859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19196603942093) ^ 9598301971046 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19196603942093) ^ 834634954004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19196603942093) ^ 9414715028 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19196603942093) ^ 187588 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_19599049775969 : Nat.Prime 19599049775969 := by
  apply lucas_primality 19599049775969 (3 : ZMod 19599049775969)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (31, 1), (6067, 1), (250499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (31, 1), (6067, 1), (250499, 1)] : List FactorBlock).map factorBlockValue).prod) = 19599049775969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_6067
      · exact prime_eightyEightCH_250499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19599049775969) ^ 9799524887984 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19599049775969) ^ 1507619213536 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19599049775969) ^ 632227412128 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19599049775969) ^ 3230435104 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19599049775969) ^ 78240032 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_23911605771583 : Nat.Prime 23911605771583 := by
  apply lucas_primality 23911605771583 (3 : ZMod 23911605771583)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (23879, 1), (478207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (23879, 1), (478207, 1)] : List FactorBlock).map factorBlockValue).prod) = 23911605771583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_349
      · exact prime_eightyEightCH_23879
      · exact prime_eightyEightCH_478207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23911605771583) ^ 11955802885791 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23911605771583) ^ 7970535257194 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23911605771583) ^ 68514629718 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23911605771583) ^ 1001365458 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23911605771583) ^ 50002626 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_29299260503663 : Nat.Prime 29299260503663 := by
  apply lucas_primality 29299260503663 (5 : ZMod 29299260503663)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (317, 1), (78460687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (317, 1), (78460687, 1)] : List FactorBlock).map factorBlockValue).prod) = 29299260503663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_317
      · exact prime_eightyEightCH_78460687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29299260503663) ^ 14649630251831 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 29299260503663) ^ 1542066342298 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 29299260503663) ^ 945137435602 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 29299260503663) ^ 92426689286 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 29299260503663) ^ 373426 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_30075560831447 : Nat.Prime 30075560831447 := by
  apply lucas_primality 30075560831447 (5 : ZMod 30075560831447)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (151, 1), (10429, 1), (734549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (151, 1), (10429, 1), (734549, 1)] : List FactorBlock).map factorBlockValue).prod) = 30075560831447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_10429
      · exact prime_eightyEightCH_734549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30075560831447) ^ 15037780415723 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 30075560831447) ^ 2313504679342 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 30075560831447) ^ 199175899546 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 30075560831447) ^ 2883839374 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 30075560831447) ^ 40944254 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_37555948299383 : Nat.Prime 37555948299383 := by
  apply lucas_primality 37555948299383 (5 : ZMod 37555948299383)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (172274992199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (172274992199, 1)] : List FactorBlock).map factorBlockValue).prod) = 37555948299383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_109
      · exact prime_eightyEightCH_172274992199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37555948299383) ^ 18777974149691 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37555948299383) ^ 344549984398 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 37555948299383) ^ 218 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_57621189848531 : Nat.Prime 57621189848531 := by
  apply lucas_primality 57621189848531 (18 : ZMod 57621189848531)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (11, 1), (31, 1), (344851217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (11, 1), (31, 1), (344851217, 1)] : List FactorBlock).map factorBlockValue).prod) = 57621189848531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_344851217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 57621189848531) ^ 28810594924265 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (18 : ZMod 57621189848531) ^ 11524237969706 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (18 : ZMod 57621189848531) ^ 8231598549790 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (18 : ZMod 57621189848531) ^ 5238289986230 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (18 : ZMod 57621189848531) ^ 1858748059630 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (18 : ZMod 57621189848531) ^ 167090 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_73520110754653 : Nat.Prime 73520110754653 := by
  apply lucas_primality 73520110754653 (2 : ZMod 73520110754653)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (6959, 1), (23794487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (6959, 1), (23794487, 1)] : List FactorBlock).map factorBlockValue).prod) = 73520110754653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_6959
      · exact prime_eightyEightCH_23794487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73520110754653) ^ 36760055377326 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73520110754653) ^ 24506703584884 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73520110754653) ^ 1987030020396 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73520110754653) ^ 10564752228 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73520110754653) ^ 3089796 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_90990351502109 : Nat.Prime 90990351502109 := by
  apply lucas_primality 90990351502109 (2 : ZMod 90990351502109)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1197241467133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1197241467133, 1)] : List FactorBlock).map factorBlockValue).prod) = 90990351502109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_1197241467133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90990351502109) ^ 45495175751054 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 90990351502109) ^ 4788965868532 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 90990351502109) ^ 76 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_175531934437121 : Nat.Prime 175531934437121 := by
  apply lucas_primality 175531934437121 (3 : ZMod 175531934437121)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (71, 1), (1931469349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (71, 1), (1931469349, 1)] : List FactorBlock).map factorBlockValue).prod) = 175531934437121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_71
      · exact prime_eightyEightCH_1931469349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 175531934437121) ^ 87765967218560 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 175531934437121) ^ 35106386887424 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 175531934437121) ^ 2472280766720 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 175531934437121) ^ 90880 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_219831312150391 : Nat.Prime 219831312150391 := by
  apply lucas_primality 219831312150391 (3 : ZMod 219831312150391)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (181, 1), (570205463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (181, 1), (570205463, 1)] : List FactorBlock).map factorBlockValue).prod) = 219831312150391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_71
      · exact prime_eightyEightCH_181
      · exact prime_eightyEightCH_570205463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 219831312150391) ^ 109915656075195 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 219831312150391) ^ 73277104050130 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 219831312150391) ^ 43966262430078 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 219831312150391) ^ 3096215664090 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 219831312150391) ^ 1214537636190 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 219831312150391) ^ 385530 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_221850821916247 : Nat.Prime 221850821916247 := by
  apply lucas_primality 221850821916247 (3 : ZMod 221850821916247)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (8069, 1), (199233443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (8069, 1), (199233443, 1)] : List FactorBlock).map factorBlockValue).prod) = 221850821916247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_8069
      · exact prime_eightyEightCH_199233443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 221850821916247) ^ 110925410958123 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221850821916247) ^ 73950273972082 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221850821916247) ^ 9645687909402 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221850821916247) ^ 27494215134 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 221850821916247) ^ 1113522 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_254283732002207 : Nat.Prime 254283732002207 := by
  apply lucas_primality 254283732002207 (5 : ZMod 254283732002207)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (2956787581421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (2956787581421, 1)] : List FactorBlock).map factorBlockValue).prod) = 254283732002207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_2956787581421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 254283732002207) ^ 127141866001103 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 254283732002207) ^ 5913575162842 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 254283732002207) ^ 86 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_260544598953029 : Nat.Prime 260544598953029 := by
  apply lucas_primality 260544598953029 (2 : ZMod 260544598953029)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (179, 1), (383, 1), (1187, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (179, 1), (383, 1), (1187, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) = 260544598953029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_179
      · exact prime_eightyEightCH_383
      · exact prime_eightyEightCH_1187
      · exact prime_eightyEightCH_2677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 260544598953029) ^ 130272299476514 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 20041892227156 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 11328026041436 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 1455556418732 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 680273104316 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 219498398444 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 260544598953029) ^ 97327082164 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_278455025774243 : Nat.Prime 278455025774243 := by
  apply lucas_primality 278455025774243 (2 : ZMod 278455025774243)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (59, 1), (24239, 1), (4232827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (59, 1), (24239, 1), (4232827, 1)] : List FactorBlock).map factorBlockValue).prod) = 278455025774243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_59
      · exact prime_eightyEightCH_24239
      · exact prime_eightyEightCH_4232827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 278455025774243) ^ 139227512887121 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 278455025774243) ^ 12106740251054 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 278455025774243) ^ 4719576708038 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 278455025774243) ^ 11487892478 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 278455025774243) ^ 65784646 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_305041387161607 : Nat.Prime 305041387161607 := by
  apply lucas_primality 305041387161607 (3 : ZMod 305041387161607)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (83, 1), (431, 1), (1033, 1), (47441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (83, 1), (431, 1), (1033, 1), (47441, 1)] : List FactorBlock).map factorBlockValue).prod) = 305041387161607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_83
      · exact prime_eightyEightCH_431
      · exact prime_eightyEightCH_1033
      · exact prime_eightyEightCH_47441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 305041387161607) ^ 152520693580803 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 101680462387202 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 10518668522814 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 3675197435682 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 707752638426 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 295296599382 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 305041387161607) ^ 6429910566 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_311379696638249 : Nat.Prime 311379696638249 := by
  apply lucas_primality 311379696638249 (3 : ZMod 311379696638249)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (101, 2), (10284511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (101, 2), (10284511, 1)] : List FactorBlock).map factorBlockValue).prod) = 311379696638249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_101
      · exact prime_eightyEightCH_10284511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 311379696638249) ^ 155689848319124 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 311379696638249) ^ 44482813805464 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 311379696638249) ^ 5875088615816 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 311379696638249) ^ 3082967293448 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 311379696638249) ^ 30276568 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_367553995923997 : Nat.Prime 367553995923997 := by
  apply lucas_primality 367553995923997 (14 : ZMod 367553995923997)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (3361, 1), (144654131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (3361, 1), (144654131, 1)] : List FactorBlock).map factorBlockValue).prod) = 367553995923997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_3361
      · exact prime_eightyEightCH_144654131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 367553995923997) ^ 183776997961998 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 367553995923997) ^ 122517998641332 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 367553995923997) ^ 52507713703428 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 367553995923997) ^ 109358523036 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 367553995923997) ^ 2540916 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_473269639267189 : Nat.Prime 473269639267189 := by
  apply lucas_primality 473269639267189 (2 : ZMod 473269639267189)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (4382126289511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (4382126289511, 1)] : List FactorBlock).map factorBlockValue).prod) = 473269639267189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_4382126289511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 473269639267189) ^ 236634819633594 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 473269639267189) ^ 157756546422396 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 473269639267189) ^ 108 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_482033777210303 : Nat.Prime 482033777210303 := by
  apply lucas_primality 482033777210303 (5 : ZMod 482033777210303)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20947, 1), (11506033733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20947, 1), (11506033733, 1)] : List FactorBlock).map factorBlockValue).prod) = 482033777210303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_20947
      · exact prime_eightyEightCH_11506033733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 482033777210303) ^ 241016888605151 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 482033777210303) ^ 23012067466 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 482033777210303) ^ 41894 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_514032590558699 : Nat.Prime 514032590558699 := by
  apply lucas_primality 514032590558699 (2 : ZMod 514032590558699)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (389, 1), (9861347323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (389, 1), (9861347323, 1)] : List FactorBlock).map factorBlockValue).prod) = 514032590558699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_67
      · exact prime_eightyEightCH_389
      · exact prime_eightyEightCH_9861347323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 514032590558699) ^ 257016295279349 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 514032590558699) ^ 7672128217294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 514032590558699) ^ 1321420541282 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 514032590558699) ^ 52126 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_525622998233131 : Nat.Prime 525622998233131 := by
  apply lucas_primality 525622998233131 (2 : ZMod 525622998233131)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (499, 1), (5015965247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (499, 1), (5015965247, 1)] : List FactorBlock).map factorBlockValue).prod) = 525622998233131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_499
      · exact prime_eightyEightCH_5015965247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 525622998233131) ^ 262811499116565 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 525622998233131) ^ 175207666077710 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 525622998233131) ^ 105124599646626 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 525622998233131) ^ 75088999747590 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 525622998233131) ^ 1053352701870 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 525622998233131) ^ 104790 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1443487387324603 : Nat.Prime 1443487387324603 := by
  apply lucas_primality 1443487387324603 (5 : ZMod 1443487387324603)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15259, 1), (15766513613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15259, 1), (15766513613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1443487387324603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_15259
      · exact prime_eightyEightCH_15766513613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1443487387324603) ^ 721743693662301 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1443487387324603) ^ 481162462441534 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1443487387324603) ^ 94599081678 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1443487387324603) ^ 91554 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2069019194763071 : Nat.Prime 2069019194763071 := by
  apply lucas_primality 2069019194763071 (11 : ZMod 2069019194763071)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (599, 1), (2273, 1), (13814831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (599, 1), (2273, 1), (13814831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2069019194763071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_599
      · exact prime_eightyEightCH_2273
      · exact prime_eightyEightCH_13814831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2069019194763071) ^ 1034509597381535 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2069019194763071) ^ 413803838952614 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2069019194763071) ^ 188092654069370 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2069019194763071) ^ 3454122194930 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2069019194763071) ^ 910259214590 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2069019194763071) ^ 149767970 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2267177613866749 : Nat.Prime 2267177613866749 := by
  apply lucas_primality 2267177613866749 (2 : ZMod 2267177613866749)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (1908398664871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (1908398664871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267177613866749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_1908398664871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2267177613866749) ^ 1133588806933374 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267177613866749) ^ 755725871288916 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267177613866749) ^ 206107055806068 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267177613866749) ^ 1188 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2273912194670231 : Nat.Prime 2273912194670231 := by
  apply lucas_primality 2273912194670231 (11 : ZMod 2273912194670231)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (607, 1), (5081, 1), (3880451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (607, 1), (5081, 1), (3880451, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273912194670231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_607
      · exact prime_eightyEightCH_5081
      · exact prime_eightyEightCH_3880451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2273912194670231) ^ 1136956097335115 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2273912194670231) ^ 454782438934046 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2273912194670231) ^ 119679589193170 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2273912194670231) ^ 3746148590890 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2273912194670231) ^ 447532413830 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2273912194670231) ^ 585991730 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2996723303401253 : Nat.Prime 2996723303401253 := by
  apply lucas_primality 2996723303401253 (2 : ZMod 2996723303401253)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7884529, 1), (95019097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7884529, 1), (95019097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2996723303401253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7884529
      · exact prime_eightyEightCH_95019097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2996723303401253) ^ 1498361651700626 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996723303401253) ^ 380076388 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2996723303401253) ^ 31538116 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4688517904326731 : Nat.Prime 4688517904326731 := by
  apply lucas_primality 4688517904326731 (10 : ZMod 4688517904326731)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (79, 1), (81299079319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (79, 1), (81299079319, 1)] : List FactorBlock).map factorBlockValue).prod) = 4688517904326731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_73
      · exact prime_eightyEightCH_79
      · exact prime_eightyEightCH_81299079319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4688517904326731) ^ 2344258952163365 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688517904326731) ^ 937703580865346 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688517904326731) ^ 64226272662010 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688517904326731) ^ 59348327902870 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 4688517904326731) ^ 57670 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4923231874221389 : Nat.Prime 4923231874221389 := by
  apply lucas_primality 4923231874221389 (3 : ZMod 4923231874221389)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (23, 1), (113, 1), (5204063983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (23, 1), (113, 1), (5204063983, 1)] : List FactorBlock).map factorBlockValue).prod) = 4923231874221389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_113
      · exact prime_eightyEightCH_5204063983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4923231874221389) ^ 2461615937110694 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4923231874221389) ^ 703318839174484 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4923231874221389) ^ 378710144170876 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4923231874221389) ^ 214053559748756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4923231874221389) ^ 43568423665676 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4923231874221389) ^ 946036 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_5993446606802507 : Nat.Prime 5993446606802507 := by
  apply lucas_primality 5993446606802507 (2 : ZMod 5993446606802507)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2996723303401253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2996723303401253, 1)] : List FactorBlock).map factorBlockValue).prod) = 5993446606802507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2996723303401253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5993446606802507) ^ 2996723303401253 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5993446606802507) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6660830533495823 : Nat.Prime 6660830533495823 := by
  apply lucas_primality 6660830533495823 (5 : ZMod 6660830533495823)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (677, 1), (1583, 1), (3107626421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (677, 1), (1583, 1), (3107626421, 1)] : List FactorBlock).map factorBlockValue).prod) = 6660830533495823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_677
      · exact prime_eightyEightCH_1583
      · exact prime_eightyEightCH_3107626421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6660830533495823) ^ 3330415266747911 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6660830533495823) ^ 9838745248886 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6660830533495823) ^ 4207726174034 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6660830533495823) ^ 2143382 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_7734445784785411 : Nat.Prime 7734445784785411 := by
  apply lucas_primality 7734445784785411 (2 : ZMod 7734445784785411)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (47, 1), (199, 1), (889191529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (47, 1), (199, 1), (889191529, 1)] : List FactorBlock).map factorBlockValue).prod) = 7734445784785411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_47
      · exact prime_eightyEightCH_199
      · exact prime_eightyEightCH_889191529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7734445784785411) ^ 3867222892392705 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 2578148594928470 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 1546889156957082 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 249498251122110 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 164562676272030 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 38866561732590 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7734445784785411) ^ 8698290 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_7811597801204839 : Nat.Prime 7811597801204839 := by
  apply lucas_primality 7811597801204839 (3 : ZMod 7811597801204839)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (23, 1), (199, 1), (2377, 1), (2099441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (23, 1), (199, 1), (2377, 1), (2099441, 1)] : List FactorBlock).map factorBlockValue).prod) = 7811597801204839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_199
      · exact prime_eightyEightCH_2377
      · exact prime_eightyEightCH_2099441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7811597801204839) ^ 3905798900602419 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 2603865933734946 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 411136726379202 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 339634687008906 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 39254260307562 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 3286326378294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7811597801204839) ^ 3720798918 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_9756384643442587 : Nat.Prime 9756384643442587 := by
  apply lucas_primality 9756384643442587 (2 : ZMod 9756384643442587)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (87719, 1), (639213581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (87719, 1), (639213581, 1)] : List FactorBlock).map factorBlockValue).prod) = 9756384643442587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_87719
      · exact prime_eightyEightCH_639213581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9756384643442587) ^ 4878192321721293 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9756384643442587) ^ 3252128214480862 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9756384643442587) ^ 336427056670434 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9756384643442587) ^ 111223163094 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9756384643442587) ^ 15263106 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_11563705961128883 : Nat.Prime 11563705961128883 := by
  apply lucas_primality 11563705961128883 (2 : ZMod 11563705961128883)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (525622998233131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (525622998233131, 1)] : List FactorBlock).map factorBlockValue).prod) = 11563705961128883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_525622998233131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11563705961128883) ^ 5781852980564441 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11563705961128883) ^ 1051245996466262 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11563705961128883) ^ 22 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_13717116251472451 : Nat.Prime 13717116251472451 := by
  apply lucas_primality 13717116251472451 (2 : ZMod 13717116251472451)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (151, 1), (605612196533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (151, 1), (605612196533, 1)] : List FactorBlock).map factorBlockValue).prod) = 13717116251472451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_605612196533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13717116251472451) ^ 6858558125736225 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13717116251472451) ^ 4572372083824150 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13717116251472451) ^ 2743423250294490 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13717116251472451) ^ 90841829479950 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13717116251472451) ^ 22650 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_16231310630193619 : Nat.Prime 16231310630193619 := by
  apply lucas_primality 16231310630193619 (2 : ZMod 16231310630193619)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (328127, 1), (24758033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (328127, 1), (24758033, 1)] : List FactorBlock).map factorBlockValue).prod) = 16231310630193619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_328127
      · exact prime_eightyEightCH_24758033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16231310630193619) ^ 8115655315096809 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16231310630193619) ^ 5410436876731206 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16231310630193619) ^ 438684071086314 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16231310630193619) ^ 49466549934 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16231310630193619) ^ 655597746 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_22692306446229019 : Nat.Prime 22692306446229019 := by
  apply lucas_primality 22692306446229019 (3 : ZMod 22692306446229019)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73721, 1), (51302221543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73721, 1), (51302221543, 1)] : List FactorBlock).map factorBlockValue).prod) = 22692306446229019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_73721
      · exact prime_eightyEightCH_51302221543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22692306446229019) ^ 11346153223114509 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 22692306446229019) ^ 7564102148743006 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 22692306446229019) ^ 307813329258 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 22692306446229019) ^ 442326 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_26110194786844481 : Nat.Prime 26110194786844481 := by
  apply lucas_primality 26110194786844481 (3 : ZMod 26110194786844481)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (13, 1), (5477, 1), (1145972089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (13, 1), (5477, 1), (1145972089, 1)] : List FactorBlock).map factorBlockValue).prod) = 26110194786844481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_5477
      · exact prime_eightyEightCH_1145972089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26110194786844481) ^ 13055097393422240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26110194786844481) ^ 5222038957368896 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26110194786844481) ^ 2008476522064960 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26110194786844481) ^ 4767243890240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26110194786844481) ^ 22784320 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_30586145814443173 : Nat.Prime 30586145814443173 := by
  apply lucas_primality 30586145814443173 (2 : ZMod 30586145814443173)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (137, 1), (3313, 1), (6389, 1), (46261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (137, 1), (3313, 1), (6389, 1), (46261, 1)] : List FactorBlock).map factorBlockValue).prod) = 30586145814443173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_137
      · exact prime_eightyEightCH_3313
      · exact prime_eightyEightCH_6389
      · exact prime_eightyEightCH_46261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30586145814443173) ^ 15293072907221586 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 10195381938147724 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 1609797148128588 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 223256538791556 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 9232159919844 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 4787313478548 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30586145814443173) ^ 661164821652 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_33616879380657851 : Nat.Prime 33616879380657851 := by
  apply lucas_primality 33616879380657851 (2 : ZMod 33616879380657851)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (131, 1), (223145565089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (131, 1), (223145565089, 1)] : List FactorBlock).map factorBlockValue).prod) = 33616879380657851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_131
      · exact prime_eightyEightCH_223145565089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33616879380657851) ^ 16808439690328925 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33616879380657851) ^ 6723375876131570 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33616879380657851) ^ 1461603451332950 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33616879380657851) ^ 256617399852350 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33616879380657851) ^ 150650 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_36692184214365341 : Nat.Prime 36692184214365341 := by
  apply lucas_primality 36692184214365341 (2 : ZMod 36692184214365341)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (30075560831447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (30075560831447, 1)] : List FactorBlock).map factorBlockValue).prod) = 36692184214365341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_61
      · exact prime_eightyEightCH_30075560831447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36692184214365341) ^ 18346092107182670 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36692184214365341) ^ 7338436842873068 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36692184214365341) ^ 601511216628940 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36692184214365341) ^ 1220 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_45975520941809297 : Nat.Prime 45975520941809297 := by
  apply lucas_primality 45975520941809297 (3 : ZMod 45975520941809297)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1889, 1), (4021, 1), (378303749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1889, 1), (4021, 1), (378303749, 1)] : List FactorBlock).map factorBlockValue).prod) = 45975520941809297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1889
      · exact prime_eightyEightCH_4021
      · exact prime_eightyEightCH_378303749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45975520941809297) ^ 22987760470904648 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45975520941809297) ^ 24338549995664 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45975520941809297) ^ 11433852509776 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45975520941809297) ^ 121530704 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_47329713889013849 : Nat.Prime 47329713889013849 := by
  apply lucas_primality 47329713889013849 (3 : ZMod 47329713889013849)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (311379696638249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (311379696638249, 1)] : List FactorBlock).map factorBlockValue).prod) = 47329713889013849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_311379696638249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47329713889013849) ^ 23664856944506924 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47329713889013849) ^ 2491037573105992 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 47329713889013849) ^ 152 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_61477970459969983 : Nat.Prime 61477970459969983 := by
  apply lucas_primality 61477970459969983 (3 : ZMod 61477970459969983)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (184081, 1), (3274239061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (184081, 1), (3274239061, 1)] : List FactorBlock).map factorBlockValue).prod) = 61477970459969983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_184081
      · exact prime_eightyEightCH_3274239061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61477970459969983) ^ 30738985229984991 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 61477970459969983) ^ 20492656819989994 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 61477970459969983) ^ 3616351203527646 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 61477970459969983) ^ 333972384222 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 61477970459969983) ^ 18776262 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_66910246556305021 : Nat.Prime 66910246556305021 := by
  apply lucas_primality 66910246556305021 (10 : ZMod 66910246556305021)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (523, 1), (193841608889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (523, 1), (193841608889, 1)] : List FactorBlock).map factorBlockValue).prod) = 66910246556305021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_523
      · exact prime_eightyEightCH_193841608889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 66910246556305021) ^ 33455123278152510 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 66910246556305021) ^ 22303415518768340 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 66910246556305021) ^ 13382049311261004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 66910246556305021) ^ 6082749686936820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 66910246556305021) ^ 127935461866740 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 66910246556305021) ^ 345180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_73384368428730683 : Nat.Prime 73384368428730683 := by
  apply lucas_primality 73384368428730683 (2 : ZMod 73384368428730683)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36692184214365341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36692184214365341, 1)] : List FactorBlock).map factorBlockValue).prod) = 73384368428730683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_36692184214365341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 73384368428730683) ^ 36692184214365341 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 73384368428730683) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_127543532386107641 : Nat.Prime 127543532386107641 := by
  apply lucas_primality 127543532386107641 (3 : ZMod 127543532386107641)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (167, 1), (1787, 1), (3359, 1), (289171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (167, 1), (1787, 1), (3359, 1), (289171, 1)] : List FactorBlock).map factorBlockValue).prod) = 127543532386107641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_167
      · exact prime_eightyEightCH_1787
      · exact prime_eightyEightCH_3359
      · exact prime_eightyEightCH_289171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 127543532386107641) ^ 63771766193053820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 25508706477221528 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 11594866580555240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 763733726862920 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 71372989583720 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 37970685437960 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 127543532386107641) ^ 441066124840 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_127951446262587769 : Nat.Prime 127951446262587769 := by
  apply lucas_primality 127951446262587769 (73 : ZMod 127951446262587769)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (83, 1), (385589, 1), (55527737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (83, 1), (385589, 1), (55527737, 1)] : List FactorBlock).map factorBlockValue).prod) = 127951446262587769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_83
      · exact prime_eightyEightCH_385589
      · exact prime_eightyEightCH_55527737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 127951446262587769) ^ 63975723131293884 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (73 : ZMod 127951446262587769) ^ 42650482087529256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (73 : ZMod 127951446262587769) ^ 1541583689910696 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (73 : ZMod 127951446262587769) ^ 331833756312 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (73 : ZMod 127951446262587769) ^ 2304279864 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_170363373534399769 : Nat.Prime 170363373534399769 := by
  apply lucas_primality 170363373534399769 (14 : ZMod 170363373534399769)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (83, 1), (3793, 1), (980338861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (83, 1), (3793, 1), (980338861, 1)] : List FactorBlock).map factorBlockValue).prod) = 170363373534399769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_83
      · exact prime_eightyEightCH_3793
      · exact prime_eightyEightCH_980338861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 170363373534399769) ^ 85181686767199884 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 170363373534399769) ^ 56787791178133256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 170363373534399769) ^ 7407103197147816 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 170363373534399769) ^ 2052570765474696 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 170363373534399769) ^ 44915205255576 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 170363373534399769) ^ 173780088 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_197722728467580577 : Nat.Prime 197722728467580577 := by
  apply lucas_primality 197722728467580577 (10 : ZMod 197722728467580577)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (29, 1), (67, 2), (3559, 1), (341953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (29, 1), (67, 2), (3559, 1), (341953, 1)] : List FactorBlock).map factorBlockValue).prod) = 197722728467580577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_67
      · exact prime_eightyEightCH_3559
      · exact prime_eightyEightCH_341953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 197722728467580577) ^ 98861364233790288 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 65907576155860192 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 15209440651352352 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 6818025119571744 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 2951085499516128 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 55555697799264 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 197722728467580577) ^ 578216095392 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_288054735061348817 : Nat.Prime 288054735061348817 := by
  apply lucas_primality 288054735061348817 (3 : ZMod 288054735061348817)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (43, 1), (181, 1), (313, 1), (671847929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (43, 1), (181, 1), (313, 1), (671847929, 1)] : List FactorBlock).map factorBlockValue).prod) = 288054735061348817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_181
      · exact prime_eightyEightCH_313
      · exact prime_eightyEightCH_671847929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 288054735061348817) ^ 144027367530674408 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288054735061348817) ^ 26186794096486256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288054735061348817) ^ 6698947327008112 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288054735061348817) ^ 1591462624648336 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288054735061348817) ^ 920302667927632 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 288054735061348817) ^ 428749904 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_363693078017562529 : Nat.Prime 363693078017562529 := by
  apply lucas_primality 363693078017562529 (7 : ZMod 363693078017562529)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (9362747, 1), (44959141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (9362747, 1), (44959141, 1)] : List FactorBlock).map factorBlockValue).prod) = 363693078017562529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_9362747
      · exact prime_eightyEightCH_44959141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 363693078017562529) ^ 181846539008781264 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 363693078017562529) ^ 121231026005854176 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 363693078017562529) ^ 38844697824 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 363693078017562529) ^ 8089413408 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_435123106858999477 : Nat.Prime 435123106858999477 := by
  apply lucas_primality 435123106858999477 (2 : ZMod 435123106858999477)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (37, 1), (41, 1), (43, 1), (50273, 1), (409523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (37, 1), (41, 1), (43, 1), (50273, 1), (409523, 1)] : List FactorBlock).map factorBlockValue).prod) = 435123106858999477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_43
      · exact prime_eightyEightCH_50273
      · exact prime_eightyEightCH_409523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435123106858999477) ^ 217561553429499738 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 145041035619666492 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 11760083969162148 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 10612758703878036 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 10119142019976732 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 8655204719412 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 435123106858999477) ^ 1062512012412 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_465021114700019641 : Nat.Prime 465021114700019641 := by
  apply lucas_primality 465021114700019641 (17 : ZMod 465021114700019641)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (307, 1), (16879, 1), (106833707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (307, 1), (16879, 1), (106833707, 1)] : List FactorBlock).map factorBlockValue).prod) = 465021114700019641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_307
      · exact prime_eightyEightCH_16879
      · exact prime_eightyEightCH_106833707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 465021114700019641) ^ 232510557350009820 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 155007038233339880 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 93004222940003928 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 66431587814288520 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 1514726757980520 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 27550276361160 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 465021114700019641) ^ 4352756520 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_469845640492965883 : Nat.Prime 469845640492965883 := by
  apply lucas_primality 469845640492965883 (3 : ZMod 469845640492965883)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1009, 1), (2874412023229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1009, 1), (2874412023229, 1)] : List FactorBlock).map factorBlockValue).prod) = 469845640492965883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1009
      · exact prime_eightyEightCH_2874412023229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 469845640492965883) ^ 234922820246482941 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 469845640492965883) ^ 156615213497655294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 469845640492965883) ^ 465654747763098 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 469845640492965883) ^ 163458 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_567956566668166189 : Nat.Prime 567956566668166189 := by
  apply lucas_primality 567956566668166189 (6 : ZMod 567956566668166189)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47329713889013849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47329713889013849, 1)] : List FactorBlock).map factorBlockValue).prod) = 567956566668166189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_47329713889013849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 567956566668166189) ^ 283978283334083094 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 567956566668166189) ^ 189318855556055396 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 567956566668166189) ^ 12 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_681453494137599077 : Nat.Prime 681453494137599077 := by
  apply lucas_primality 681453494137599077 (2 : ZMod 681453494137599077)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (170363373534399769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (170363373534399769, 1)] : List FactorBlock).map factorBlockValue).prod) = 681453494137599077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_170363373534399769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 681453494137599077) ^ 340726747068799538 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 681453494137599077) ^ 4 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1039928957691067883 : Nat.Prime 1039928957691067883 := by
  apply lucas_primality 1039928957691067883 (2 : ZMod 1039928957691067883)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (30586145814443173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (30586145814443173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039928957691067883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_30586145814443173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1039928957691067883) ^ 519964478845533941 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039928957691067883) ^ 61172291628886346 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1039928957691067883) ^ 34 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1265027929543621729 : Nat.Prime 1265027929543621729 := by
  apply lucas_primality 1265027929543621729 (7 : ZMod 1265027929543621729)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (443, 1), (617, 1), (16070105801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (443, 1), (617, 1), (16070105801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1265027929543621729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_443
      · exact prime_eightyEightCH_617
      · exact prime_eightyEightCH_16070105801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1265027929543621729) ^ 632513964771810864 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1265027929543621729) ^ 421675976514540576 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1265027929543621729) ^ 2855593520414496 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1265027929543621729) ^ 2050288378514784 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1265027929543621729) ^ 78719328 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1499496002260129067 : Nat.Prime 1499496002260129067 := by
  apply lucas_primality 1499496002260129067 (5 : ZMod 1499496002260129067)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (4566941, 1), (95613589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (4566941, 1), (95613589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1499496002260129067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_101
      · exact prime_eightyEightCH_4566941
      · exact prime_eightyEightCH_95613589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1499496002260129067) ^ 749748001130064533 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1499496002260129067) ^ 88205647191772298 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1499496002260129067) ^ 14846495071882466 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1499496002260129067) ^ 328337064626 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1499496002260129067) ^ 15682875394 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4070447899881399721 : Nat.Prime 4070447899881399721 := by
  apply lucas_primality 4070447899881399721 (14 : ZMod 4070447899881399721)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (19, 1), (31, 1), (19196603942093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (19, 1), (31, 1), (19196603942093, 1)] : List FactorBlock).map factorBlockValue).prod) = 4070447899881399721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_31
      · exact prime_eightyEightCH_19196603942093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4070447899881399721) ^ 2035223949940699860 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 4070447899881399721) ^ 1356815966627133240 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 4070447899881399721) ^ 814089579976279944 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 4070447899881399721) ^ 214234099993757880 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 4070447899881399721) ^ 131304770963916120 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (14 : ZMod 4070447899881399721) ^ 212040 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_4172848256161254487 : Nat.Prime 4172848256161254487 := by
  apply lucas_primality 4172848256161254487 (3 : ZMod 4172848256161254487)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6826271, 1), (101882083111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6826271, 1), (101882083111, 1)] : List FactorBlock).map factorBlockValue).prod) = 4172848256161254487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_6826271
      · exact prime_eightyEightCH_101882083111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4172848256161254487) ^ 2086424128080627243 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4172848256161254487) ^ 1390949418720418162 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4172848256161254487) ^ 611292498666 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4172848256161254487) ^ 40957626 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_6239573746146407299 : Nat.Prime 6239573746146407299 := by
  apply lucas_primality 6239573746146407299 (3 : ZMod 6239573746146407299)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1039928957691067883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1039928957691067883, 1)] : List FactorBlock).map factorBlockValue).prod) = 6239573746146407299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1039928957691067883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6239573746146407299) ^ 3119786873073203649 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6239573746146407299) ^ 2079857915382135766 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6239573746146407299) ^ 6 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_7092486134968332227 : Nat.Prime 7092486134968332227 := by
  apply lucas_primality 7092486134968332227 (2 : ZMod 7092486134968332227)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (66910246556305021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (66910246556305021, 1)] : List FactorBlock).map factorBlockValue).prod) = 7092486134968332227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_66910246556305021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7092486134968332227) ^ 3546243067484166113 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7092486134968332227) ^ 133820493112610042 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7092486134968332227) ^ 106 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_16691393024645017949 : Nat.Prime 16691393024645017949 := by
  apply lucas_primality 16691393024645017949 (2 : ZMod 16691393024645017949)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4172848256161254487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4172848256161254487, 1)] : List FactorBlock).map factorBlockValue).prod) = 16691393024645017949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_4172848256161254487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16691393024645017949) ^ 8345696512322508974 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 16691393024645017949) ^ 4 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_19060789397416174981 : Nat.Prime 19060789397416174981 := by
  apply lucas_primality 19060789397416174981 (7 : ZMod 19060789397416174981)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 1), (13, 1), (23, 1), (971, 1), (1913, 1), (5777621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 1), (13, 1), (23, 1), (971, 1), (1913, 1), (5777621, 1)] : List FactorBlock).map factorBlockValue).prod) = 19060789397416174981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_13
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_971
      · exact prime_eightyEightCH_1913
      · exact prime_eightyEightCH_5777621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19060789397416174981) ^ 9530394698708087490 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 6353596465805391660 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 3812157879483234996 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 1732799036128743180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 1466214569032013460 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 828729973800703260 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 19630061171386380 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 9963820908215460 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 19060789397416174981) ^ 3299072299380 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_21750845945632442519 : Nat.Prime 21750845945632442519 := by
  apply lucas_primality 21750845945632442519 (19 : ZMod 21750845945632442519)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (109, 1), (577, 1), (1549, 1), (349946573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (109, 1), (577, 1), (1549, 1), (349946573, 1)] : List FactorBlock).map factorBlockValue).prod) = 21750845945632442519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_109
      · exact prime_eightyEightCH_577
      · exact prime_eightyEightCH_1549
      · exact prime_eightyEightCH_349946573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 21750845945632442519) ^ 10875422972816221259 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 1977349631421131138 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 750029170539049742 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 199549045372774702 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 37696440113747734 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 14041863102409582 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (19 : ZMod 21750845945632442519) ^ 62154761966 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_32605077230948625239 : Nat.Prime 32605077230948625239 := by
  apply lucas_primality 32605077230948625239 (7 : ZMod 32605077230948625239)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3313, 1), (9128123, 1), (49007171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3313, 1), (9128123, 1), (49007171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32605077230948625239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_3313
      · exact prime_eightyEightCH_9128123
      · exact prime_eightyEightCH_49007171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32605077230948625239) ^ 16302538615474312619 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32605077230948625239) ^ 2964097930086238658 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32605077230948625239) ^ 9841556664940726 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32605077230948625239) ^ 3571936665506 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 32605077230948625239) ^ 665312372978 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_33382786049290035899 : Nat.Prime 33382786049290035899 := by
  apply lucas_primality 33382786049290035899 (2 : ZMod 33382786049290035899)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16691393024645017949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16691393024645017949, 1)] : List FactorBlock).map factorBlockValue).prod) = 33382786049290035899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_16691393024645017949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33382786049290035899) ^ 16691393024645017949 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33382786049290035899) ^ 2 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_104638533873499717733 : Nat.Prime 104638533873499717733 := by
  apply lucas_primality 104638533873499717733 (2 : ZMod 104638533873499717733)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (7493621, 1), (32026791497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (7493621, 1), (32026791497, 1)] : List FactorBlock).map factorBlockValue).prod) = 104638533873499717733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_109
      · exact prime_eightyEightCH_7493621
      · exact prime_eightyEightCH_32026791497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104638533873499717733) ^ 52319266936749858866 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 104638533873499717733) ^ 959986549298162548 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 104638533873499717733) ^ 13963681092692 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 104638533873499717733) ^ 3267218756 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_145928357578959846029 : Nat.Prime 145928357578959846029 := by
  apply lucas_primality 145928357578959846029 (2 : ZMod 145928357578959846029)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (151, 1), (90439, 1), (24508713007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (151, 1), (90439, 1), (24508713007, 1)] : List FactorBlock).map factorBlockValue).prod) = 145928357578959846029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_109
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_90439
      · exact prime_eightyEightCH_24508713007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145928357578959846029) ^ 72964178789479923014 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 145928357578959846029) ^ 1338792271366604092 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 145928357578959846029) ^ 966412964099071828 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 145928357578959846029) ^ 1613555629528852 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 145928357578959846029) ^ 5954142004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_231268473771637784497 : Nat.Prime 231268473771637784497 := by
  apply lucas_primality 231268473771637784497 (5 : ZMod 231268473771637784497)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (29, 1), (173, 1), (19599049775969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (29, 1), (173, 1), (19599049775969, 1)] : List FactorBlock).map factorBlockValue).prod) = 231268473771637784497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_173
      · exact prime_eightyEightCH_19599049775969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 231268473771637784497) ^ 115634236885818892248 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 231268473771637784497) ^ 77089491257212594832 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 231268473771637784497) ^ 33038353395948254928 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 231268473771637784497) ^ 7974774957642682224 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 231268473771637784497) ^ 1336811987119293552 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 231268473771637784497) ^ 11799984 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_368506391975960948093 : Nat.Prime 368506391975960948093 := by
  apply lucas_primality 368506391975960948093 (2 : ZMod 368506391975960948093)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (773, 1), (1232069, 1), (96732076279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (773, 1), (1232069, 1), (96732076279, 1)] : List FactorBlock).map factorBlockValue).prod) = 368506391975960948093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_773
      · exact prime_eightyEightCH_1232069
      · exact prime_eightyEightCH_96732076279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 368506391975960948093) ^ 184253195987980474046 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368506391975960948093) ^ 476722369955965004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368506391975960948093) ^ 299095579854668 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368506391975960948093) ^ 3809557348 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_482787437446134506159 : Nat.Prime 482787437446134506159 := by
  apply lucas_primality 482787437446134506159 (11 : ZMod 482787437446134506159)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3319, 1), (4351349, 1), (1519504919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3319, 1), (4351349, 1), (1519504919, 1)] : List FactorBlock).map factorBlockValue).prod) = 482787437446134506159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_3319
      · exact prime_eightyEightCH_4351349
      · exact prime_eightyEightCH_1519504919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 482787437446134506159) ^ 241393718723067253079 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 482787437446134506159) ^ 43889767040557682378 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 482787437446134506159) ^ 145461716615286082 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 482787437446134506159) ^ 110951210175542 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (11 : ZMod 482787437446134506159) ^ 317726801282 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1418066300311730387749 : Nat.Prime 1418066300311730387749 := by
  apply lucas_primality 1418066300311730387749 (2 : ZMod 1418066300311730387749)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (53, 1), (14851, 1), (261463, 1), (10073923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (53, 1), (14851, 1), (261463, 1), (10073923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1418066300311730387749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_19
      · exact prime_eightyEightCH_53
      · exact prime_eightyEightCH_14851
      · exact prime_eightyEightCH_261463
      · exact prime_eightyEightCH_10073923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1418066300311730387749) ^ 709033150155865193874 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 472688766770576795916 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 74635068437459494092 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 26755967930410007316 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 95486250105159948 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 5423583070307196 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418066300311730387749) ^ 140766045195276 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1420175159365398756497 : Nat.Prime 1420175159365398756497 := by
  apply lucas_primality 1420175159365398756497 (3 : ZMod 1420175159365398756497)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (149, 1), (4923231874221389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (149, 1), (4923231874221389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1420175159365398756497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_149
      · exact prime_eightyEightCH_4923231874221389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1420175159365398756497) ^ 710087579682699378248 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1420175159365398756497) ^ 129106832669581705136 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1420175159365398756497) ^ 9531376908492609104 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1420175159365398756497) ^ 288464 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2296087960135981223297 : Nat.Prime 2296087960135981223297 := by
  apply lucas_primality 2296087960135981223297 (3 : ZMod 2296087960135981223297)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (79, 1), (7455937, 1), (4350620387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (79, 1), (7455937, 1), (4350620387, 1)] : List FactorBlock).map factorBlockValue).prod) = 2296087960135981223297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_79
      · exact prime_eightyEightCH_7455937
      · exact prime_eightyEightCH_4350620387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2296087960135981223297) ^ 1148043980067990611648 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2296087960135981223297) ^ 328012565733711603328 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2296087960135981223297) ^ 29064404558683306624 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2296087960135981223297) ^ 307954313473408 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2296087960135981223297) ^ 527761044608 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2475643577734982680903 : Nat.Prime 2475643577734982680903 := by
  apply lucas_primality 2475643577734982680903 (5 : ZMod 2475643577734982680903)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (127, 1), (9756384643442587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (127, 1), (9756384643442587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2475643577734982680903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_37
      · exact prime_eightyEightCH_127
      · exact prime_eightyEightCH_9756384643442587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2475643577734982680903) ^ 1237821788867491340451 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2475643577734982680903) ^ 825214525911660893634 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2475643577734982680903) ^ 66909285884729261646 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2475643577734982680903) ^ 19493256517598288826 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2475643577734982680903) ^ 253746 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_2511324812963993225593 : Nat.Prime 2511324812963993225593 := by
  apply lucas_primality 2511324812963993225593 (15 : ZMod 2511324812963993225593)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (104638533873499717733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (104638533873499717733, 1)] : List FactorBlock).map factorBlockValue).prod) = 2511324812963993225593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_104638533873499717733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 2511324812963993225593) ^ 1255662406481996612796 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 2511324812963993225593) ^ 837108270987997741864 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (15 : ZMod 2511324812963993225593) ^ 24 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3670221484040732418859 : Nat.Prime 3670221484040732418859 := by
  apply lucas_primality 3670221484040732418859 (2 : ZMod 3670221484040732418859)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2707, 1), (137957, 1), (1637981624057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2707, 1), (137957, 1), (1637981624057, 1)] : List FactorBlock).map factorBlockValue).prod) = 3670221484040732418859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_2707
      · exact prime_eightyEightCH_137957
      · exact prime_eightyEightCH_1637981624057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3670221484040732418859) ^ 1835110742020366209429 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3670221484040732418859) ^ 1223407161346910806286 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3670221484040732418859) ^ 1355826185460189294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3670221484040732418859) ^ 26604097537933794 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3670221484040732418859) ^ 2240697594 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_7417659635615178324941 : Nat.Prime 7417659635615178324941 := by
  apply lucas_primality 7417659635615178324941 (2 : ZMod 7417659635615178324941)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (14795394697, 1), (25067461151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (14795394697, 1), (25067461151, 1)] : List FactorBlock).map factorBlockValue).prod) = 7417659635615178324941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_14795394697
      · exact prime_eightyEightCH_25067461151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7417659635615178324941) ^ 3708829817807589162470 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7417659635615178324941) ^ 1483531927123035664988 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7417659635615178324941) ^ 501349223020 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7417659635615178324941) ^ 295907893940 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_9074669249266135331951 : Nat.Prime 9074669249266135331951 := by
  apply lucas_primality 9074669249266135331951 (17 : ZMod 9074669249266135331951)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (3067, 1), (367553995923997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (3067, 1), (367553995923997, 1)] : List FactorBlock).map factorBlockValue).prod) = 9074669249266135331951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_3067
      · exact prime_eightyEightCH_367553995923997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 9074669249266135331951) ^ 4537334624633067665975 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 9074669249266135331951) ^ 1814933849853227066390 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 9074669249266135331951) ^ 1296381321323733618850 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 9074669249266135331951) ^ 394550836924614579650 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 9074669249266135331951) ^ 2958809667188175850 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 9074669249266135331951) ^ 24689350 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_17093059188221629717393 : Nat.Prime 17093059188221629717393 := by
  apply lucas_primality 17093059188221629717393 (5 : ZMod 17093059188221629717393)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (94421, 1), (221850821916247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (94421, 1), (221850821916247, 1)] : List FactorBlock).map factorBlockValue).prod) = 17093059188221629717393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_94421
      · exact prime_eightyEightCH_221850821916247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17093059188221629717393) ^ 8546529594110814858696 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17093059188221629717393) ^ 5697686396073876572464 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17093059188221629717393) ^ 1005474069895389983376 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17093059188221629717393) ^ 181030270683657552 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17093059188221629717393) ^ 77047536 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_36200918806772420477281 : Nat.Prime 36200918806772420477281 := by
  apply lucas_primality 36200918806772420477281 (39 : ZMod 36200918806772420477281)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 2), (199, 1), (7734445784785411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 2), (199, 1), (7734445784785411, 1)] : List FactorBlock).map factorBlockValue).prod) = 36200918806772420477281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_199
      · exact prime_eightyEightCH_7734445784785411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 36200918806772420477281) ^ 18100459403386210238640 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (39 : ZMod 36200918806772420477281) ^ 12066972935590806825760 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (39 : ZMod 36200918806772420477281) ^ 7240183761354484095456 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (39 : ZMod 36200918806772420477281) ^ 5171559829538917211040 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (39 : ZMod 36200918806772420477281) ^ 181914164858152866720 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (39 : ZMod 36200918806772420477281) ^ 4680480 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_40980659664672389731387 : Nat.Prime 40980659664672389731387 := by
  apply lucas_primality 40980659664672389731387 (2 : ZMod 40980659664672389731387)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1747, 1), (36815021, 1), (106196385913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1747, 1), (36815021, 1), (106196385913, 1)] : List FactorBlock).map factorBlockValue).prod) = 40980659664672389731387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_1747
      · exact prime_eightyEightCH_36815021
      · exact prime_eightyEightCH_106196385913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40980659664672389731387) ^ 20490329832336194865693 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40980659664672389731387) ^ 13660219888224129910462 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40980659664672389731387) ^ 23457733065067195038 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40980659664672389731387) ^ 1113150517140066 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 40980659664672389731387) ^ 385895050122 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_52265889105265432926869 : Nat.Prime 52265889105265432926869 := by
  apply lucas_primality 52265889105265432926869 (2 : ZMod 52265889105265432926869)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (89, 1), (139, 1), (13717116251472451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (89, 1), (139, 1), (13717116251472451, 1)] : List FactorBlock).map factorBlockValue).prod) = 52265889105265432926869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_89
      · exact prime_eightyEightCH_139
      · exact prime_eightyEightCH_13717116251472451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52265889105265432926869) ^ 26132944552632716463434 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52265889105265432926869) ^ 7466555586466490418124 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52265889105265432926869) ^ 4751444464115039356988 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52265889105265432926869) ^ 587257180958038572212 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52265889105265432926869) ^ 376013590685362826812 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 52265889105265432926869) ^ 3810268 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_119415277519134626057543 : Nat.Prime 119415277519134626057543 := by
  apply lucas_primality 119415277519134626057543 (5 : ZMod 119415277519134626057543)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2562816161, 1), (1370451028883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2562816161, 1), (1370451028883, 1)] : List FactorBlock).map factorBlockValue).prod) = 119415277519134626057543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_2562816161
      · exact prime_eightyEightCH_1370451028883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119415277519134626057543) ^ 59707638759567313028771 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 119415277519134626057543) ^ 7024428089360860356326 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 119415277519134626057543) ^ 46595334982022 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 119415277519134626057543) ^ 87135749474 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_144836231233840351847701 : Nat.Prime 144836231233840351847701 := by
  apply lucas_primality 144836231233840351847701 (6 : ZMod 144836231233840351847701)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (482787437446134506159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (482787437446134506159, 1)] : List FactorBlock).map factorBlockValue).prod) = 144836231233840351847701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_482787437446134506159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 144836231233840351847701) ^ 72418115616920175923850 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144836231233840351847701) ^ 48278743744613450615900 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144836231233840351847701) ^ 28967246246768070369540 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144836231233840351847701) ^ 300 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_169753959641707681618381 : Nat.Prime 169753959641707681618381 := by
  apply lucas_primality 169753959641707681618381 (2 : ZMod 169753959641707681618381)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (71, 1), (149, 1), (402187439, 1), (664960033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (71, 1), (149, 1), (402187439, 1), (664960033, 1)] : List FactorBlock).map factorBlockValue).prod) = 169753959641707681618381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_71
      · exact prime_eightyEightCH_149
      · exact prime_eightyEightCH_402187439
      · exact prime_eightyEightCH_664960033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169753959641707681618381) ^ 84876979820853840809190 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 56584653213902560539460 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 33950791928341536323676 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 2390900840024051853780 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 1139288319743004574620 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 422076731346420 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 169753959641707681618381) ^ 255284455030860 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_738329495011414008324343 : Nat.Prime 738329495011414008324343 := by
  apply lucas_primality 738329495011414008324343 (5 : ZMod 738329495011414008324343)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (2511324812963993225593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (2511324812963993225593, 1)] : List FactorBlock).map factorBlockValue).prod) = 738329495011414008324343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_2511324812963993225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 738329495011414008324343) ^ 369164747505707004162171 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 738329495011414008324343) ^ 246109831670471336108114 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 738329495011414008324343) ^ 105475642144487715474906 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 738329495011414008324343) ^ 294 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_751241864402111132507761 : Nat.Prime 751241864402111132507761 := by
  apply lucas_primality 751241864402111132507761 (7 : ZMod 751241864402111132507761)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (769, 1), (4070447899881399721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (769, 1), (4070447899881399721, 1)] : List FactorBlock).map factorBlockValue).prod) = 751241864402111132507761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_769
      · exact prime_eightyEightCH_4070447899881399721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 751241864402111132507761) ^ 375620932201055566253880 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 751241864402111132507761) ^ 250413954800703710835920 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 751241864402111132507761) ^ 150248372880422226501552 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 751241864402111132507761) ^ 976907495971535933040 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (7 : ZMod 751241864402111132507761) ^ 184560 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_901313215696375936628807 : Nat.Prime 901313215696375936628807 := by
  apply lucas_primality 901313215696375936628807 (5 : ZMod 901313215696375936628807)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2029, 1), (4831, 1), (45975520941809297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2029, 1), (4831, 1), (45975520941809297, 1)] : List FactorBlock).map factorBlockValue).prod) = 901313215696375936628807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2029
      · exact prime_eightyEightCH_4831
      · exact prime_eightyEightCH_45975520941809297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 901313215696375936628807) ^ 450656607848187968314403 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 901313215696375936628807) ^ 444215483339761427614 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 901313215696375936628807) ^ 186568663981862127226 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 901313215696375936628807) ^ 19604198 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3166722036922395164698357 : Nat.Prime 3166722036922395164698357 := by
  apply lucas_primality 3166722036922395164698357 (2 : ZMod 3166722036922395164698357)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (5510237, 1), (305041387161607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (5510237, 1), (305041387161607, 1)] : List FactorBlock).map factorBlockValue).prod) = 3166722036922395164698357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_157
      · exact prime_eightyEightCH_5510237
      · exact prime_eightyEightCH_305041387161607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3166722036922395164698357) ^ 1583361018461197582349178 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166722036922395164698357) ^ 1055574012307465054899452 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166722036922395164698357) ^ 20170204056830542450308 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166722036922395164698357) ^ 574697973412467588 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3166722036922395164698357) ^ 10381286508 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3557270345712325050124793 : Nat.Prime 3557270345712325050124793 := by
  apply lucas_primality 3557270345712325050124793 (5 : ZMod 3557270345712325050124793)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (9074669249266135331951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (9074669249266135331951, 1)] : List FactorBlock).map factorBlockValue).prod) = 3557270345712325050124793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_9074669249266135331951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3557270345712325050124793) ^ 1778635172856162525062396 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3557270345712325050124793) ^ 508181477958903578589256 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3557270345712325050124793) ^ 392 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3572171186302089982523599 : Nat.Prime 3572171186302089982523599 := by
  apply lucas_primality 3572171186302089982523599 (3 : ZMod 3572171186302089982523599)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (1733, 1), (924656599, 1), (1830231133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (1733, 1), (924656599, 1), (1830231133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3572171186302089982523599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_7
      · exact prime_eightyEightCH_29
      · exact prime_eightyEightCH_1733
      · exact prime_eightyEightCH_924656599
      · exact prime_eightyEightCH_1830231133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3572171186302089982523599) ^ 1786085593151044991261799 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 1190723728767363327507866 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 510310169471727140360514 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 123178316769037585604262 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 2061264389095262540406 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 3863240894149602 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3572171186302089982523599) ^ 1951759601229606 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_5453660732874580423599089 : Nat.Prime 5453660732874580423599089 := by
  apply lucas_primality 5453660732874580423599089 (3 : ZMod 5453660732874580423599089)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (12860606657, 1), (1152335239513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (12860606657, 1), (1152335239513, 1)] : List FactorBlock).map factorBlockValue).prod) = 5453660732874580423599089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_12860606657
      · exact prime_eightyEightCH_1152335239513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5453660732874580423599089) ^ 2726830366437290211799544 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5453660732874580423599089) ^ 237115684038025235808656 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5453660732874580423599089) ^ 424059368140784 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5453660732874580423599089) ^ 4732703249776 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_17139948237405003416968669 : Nat.Prime 17139948237405003416968669 := by
  apply lucas_primality 17139948237405003416968669 (6 : ZMod 17139948237405003416968669)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (239, 1), (347, 1), (94889, 1), (4426914739417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (239, 1), (347, 1), (94889, 1), (4426914739417, 1)] : List FactorBlock).map factorBlockValue).prod) = 17139948237405003416968669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_41
      · exact prime_eightyEightCH_239
      · exact prime_eightyEightCH_347
      · exact prime_eightyEightCH_94889
      · exact prime_eightyEightCH_4426914739417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17139948237405003416968669) ^ 8569974118702501708484334 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 5713316079135001138989556 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 418047517985487888218748 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 71715264591652733962212 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 49394663508371767772244 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 180631561481362470012 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 17139948237405003416968669) ^ 3871759283004 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_22850754623555539367669629 : Nat.Prime 22850754623555539367669629 := by
  apply lucas_primality 22850754623555539367669629 (17 : ZMod 22850754623555539367669629)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (1693, 1), (3037, 1), (2069019194763071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (1693, 1), (3037, 1), (2069019194763071, 1)] : List FactorBlock).map factorBlockValue).prod) = 22850754623555539367669629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_179
      · exact prime_eightyEightCH_1693
      · exact prime_eightyEightCH_3037
      · exact prime_eightyEightCH_2069019194763071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 22850754623555539367669629) ^ 11425377311777769683834814 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 22850754623555539367669629) ^ 7616918207851846455889876 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 22850754623555539367669629) ^ 127657847058969493674132 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 22850754623555539367669629) ^ 13497197060576219354796 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 22850754623555539367669629) ^ 7524120718984372528044 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (17 : ZMod 22850754623555539367669629) ^ 11044244868 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_132365758016600980586513767 : Nat.Prime 132365758016600980586513767 := by
  apply lucas_primality 132365758016600980586513767 (6 : ZMod 132365758016600980586513767)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (151, 1), (2917, 1), (54491527, 1), (27852751613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (151, 1), (2917, 1), (54491527, 1), (27852751613, 1)] : List FactorBlock).map factorBlockValue).prod) = 132365758016600980586513767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_11
      · exact prime_eightyEightCH_151
      · exact prime_eightyEightCH_2917
      · exact prime_eightyEightCH_54491527
      · exact prime_eightyEightCH_27852751613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 132365758016600980586513767) ^ 66182879008300490293256883 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 44121919338866993528837922 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 12033250728781907326046706 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 876594423950999871433866 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 45377359621734995058798 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 2429107153055207658 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 132365758016600980586513767) ^ 4752340445775582 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_144700258415922629681501837 : Nat.Prime 144700258415922629681501837 := by
  apply lucas_primality 144700258415922629681501837 (2 : ZMod 144700258415922629681501837)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (21432751, 1), (73384368428730683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (21432751, 1), (73384368428730683, 1)] : List FactorBlock).map factorBlockValue).prod) = 144700258415922629681501837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_21432751
      · exact prime_eightyEightCH_73384368428730683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144700258415922629681501837) ^ 72350129207961314840750918 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144700258415922629681501837) ^ 6291315583300983899195732 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144700258415922629681501837) ^ 6751361895443222836 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144700258415922629681501837) ^ 1971813092 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_287401894478034173317679063 : Nat.Prime 287401894478034173317679063 := by
  apply lucas_primality 287401894478034173317679063 (5 : ZMod 287401894478034173317679063)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2493890661001, 1), (57621189848531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2493890661001, 1), (57621189848531, 1)] : List FactorBlock).map factorBlockValue).prod) = 287401894478034173317679063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_2493890661001
      · exact prime_eightyEightCH_57621189848531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 287401894478034173317679063) ^ 143700947239017086658839531 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 287401894478034173317679063) ^ 115242379697062 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (5 : ZMod 287401894478034173317679063) ^ 4987781322002 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_433497857504368211420832587 : Nat.Prime 433497857504368211420832587 := by
  apply lucas_primality 433497857504368211420832587 (2 : ZMod 433497857504368211420832587)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1297, 1), (48823, 1), (91141, 1), (37555948299383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1297, 1), (48823, 1), (91141, 1), (37555948299383, 1)] : List FactorBlock).map factorBlockValue).prod) = 433497857504368211420832587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_1297
      · exact prime_eightyEightCH_48823
      · exact prime_eightyEightCH_91141
      · exact prime_eightyEightCH_37555948299383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 433497857504368211420832587) ^ 216748928752184105710416293 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 433497857504368211420832587) ^ 334231193141378728928938 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 433497857504368211420832587) ^ 8878968058176847211782 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 433497857504368211420832587) ^ 4756343001551093486146 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 433497857504368211420832587) ^ 11542721649542 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_874281393286120762529410259 : Nat.Prime 874281393286120762529410259 := by
  apply lucas_primality 874281393286120762529410259 (2 : ZMod 874281393286120762529410259)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10667, 1), (40980659664672389731387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10667, 1), (40980659664672389731387, 1)] : List FactorBlock).map factorBlockValue).prod) = 874281393286120762529410259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_10667
      · exact prime_eightyEightCH_40980659664672389731387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 874281393286120762529410259) ^ 437140696643060381264705129 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 874281393286120762529410259) ^ 81961319329344779462774 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 874281393286120762529410259) ^ 21334 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_1486278368586405296299997441 : Nat.Prime 1486278368586405296299997441 := by
  apply lucas_primality 1486278368586405296299997441 (3 : ZMod 1486278368586405296299997441)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (419, 1), (81409, 1), (1196537, 1), (28449694799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (419, 1), (81409, 1), (1196537, 1), (28449694799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1486278368586405296299997441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_419
      · exact prime_eightyEightCH_81409
      · exact prime_eightyEightCH_1196537
      · exact prime_eightyEightCH_28449694799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1486278368586405296299997441) ^ 743139184293202648149998720 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486278368586405296299997441) ^ 297255673717281059259999488 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486278368586405296299997441) ^ 3547203743642972067541760 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486278368586405296299997441) ^ 18256929437610157308160 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486278368586405296299997441) ^ 1242149944871245349120 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486278368586405296299997441) ^ 52242330861090560 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_3152711690940859719424236997 : Nat.Prime 3152711690940859719424236997 := by
  apply lucas_primality 3152711690940859719424236997 (13 : ZMod 3152711690940859719424236997)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (740461, 1), (26324773, 1), (50105327719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (740461, 1), (26324773, 1), (50105327719, 1)] : List FactorBlock).map factorBlockValue).prod) = 3152711690940859719424236997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_269
      · exact prime_eightyEightCH_740461
      · exact prime_eightyEightCH_26324773
      · exact prime_eightyEightCH_50105327719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3152711690940859719424236997) ^ 1576355845470429859712118498 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3152711690940859719424236997) ^ 1050903896980286573141412332 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3152711690940859719424236997) ^ 11720117810189069588937684 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3152711690940859719424236997) ^ 4257768729130716836436 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3152711690940859719424236997) ^ 119762160567950945652 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3152711690940859719424236997) ^ 62921685865859484 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_8003037369311413133923063141 : Nat.Prime 8003037369311413133923063141 := by
  apply lucas_primality 8003037369311413133923063141 (10 : ZMod 8003037369311413133923063141)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (769, 1), (1241115061, 1), (6076274325917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (769, 1), (1241115061, 1), (6076274325917, 1)] : List FactorBlock).map factorBlockValue).prod) = 8003037369311413133923063141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_5
      · exact prime_eightyEightCH_23
      · exact prime_eightyEightCH_769
      · exact prime_eightyEightCH_1241115061
      · exact prime_eightyEightCH_6076274325917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8003037369311413133923063141) ^ 4001518684655706566961531570 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 2667679123103804377974354380 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 1600607473862282626784612628 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 347958146491800571040133180 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 10407070701315231643593060 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 6448263840149638740 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (10 : ZMod 8003037369311413133923063141) ^ 1317096125034420 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_20807897160209674148199964163 : Nat.Prime 20807897160209674148199964163 := by
  apply lucas_primality 20807897160209674148199964163 (2 : ZMod 20807897160209674148199964163)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41611, 1), (897914497, 1), (278455025774243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41611, 1), (897914497, 1), (278455025774243, 1)] : List FactorBlock).map factorBlockValue).prod) = 20807897160209674148199964163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_41611
      · exact prime_eightyEightCH_897914497
      · exact prime_eightyEightCH_278455025774243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20807897160209674148199964163) ^ 10403948580104837074099982081 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20807897160209674148199964163) ^ 500057608810402877801542 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20807897160209674148199964163) ^ 23173584154984050946 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20807897160209674148199964163) ^ 74726240269334 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_52019742900524185370499910447 : Nat.Prime 52019742900524185370499910447 := by
  apply lucas_primality 52019742900524185370499910447 (6 : ZMod 52019742900524185370499910447)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (103239881, 1), (435123106858999477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (103239881, 1), (435123106858999477, 1)] : List FactorBlock).map factorBlockValue).prod) = 52019742900524185370499910447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_193
      · exact prime_eightyEightCH_103239881
      · exact prime_eightyEightCH_435123106858999477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 52019742900524185370499910447) ^ 26009871450262092685249955223 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 52019742900524185370499910447) ^ 17339914300174728456833303482 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 52019742900524185370499910447) ^ 269532346634840338707253422 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 52019742900524185370499910447) ^ 503872557742721394366 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (6 : ZMod 52019742900524185370499910447) ^ 119551782198 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_104039485801048370740999820839 : Nat.Prime 104039485801048370740999820839 := by
  apply lucas_primality 104039485801048370740999820839 (3 : ZMod 104039485801048370740999820839)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (199, 1), (691, 1), (7417659635615178324941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (199, 1), (691, 1), (7417659635615178324941, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_17
      · exact prime_eightyEightCH_199
      · exact prime_eightyEightCH_691
      · exact prime_eightyEightCH_7417659635615178324941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104039485801048370740999820839) ^ 52019742900524185370499910419 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820839) ^ 34679828600349456913666606946 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820839) ^ 6119969753002845337705871814 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820839) ^ 522811486437428998698491562 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820839) ^ 150563655283716889639652418 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820839) ^ 14025918 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem prime_eightyEightCH_104039485801048370740999820887 : Nat.Prime 104039485801048370740999820887 := by
  apply lucas_primality 104039485801048370740999820887 (3 : ZMod 104039485801048370740999820887)
  · rw [← eightyEightCHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (6290827, 1), (603537953, 1), (507448659539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (6290827, 1), (603537953, 1), (507448659539, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyEightCH_2
      · exact prime_eightyEightCH_3
      · exact prime_eightyEightCH_6290827
      · exact prime_eightyEightCH_603537953
      · exact prime_eightyEightCH_507448659539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104039485801048370740999820887) ^ 52019742900524185370499910443 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820887) ^ 34679828600349456913666606962 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820887) ^ 16538284362461147118018 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820887) ^ 172382673341254432662 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide
    · change (3 : ZMod 104039485801048370740999820887) ^ 205024653913885074 ≠ 1
      rw [← eightyEightCHFastPow_eq_pow]
      decide

private theorem phi_eightyEightCH_104039485801048370740999820800 : Nat.totient 104039485801048370740999820800 = 35585081094328005621228503040 := by
  rw [← show ((([(2, 9), (5, 2), (7, 1), (419, 1), (81409, 1), (1196537, 1), (28449694799, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_7, prime_eightyEightCH_419, prime_eightyEightCH_81409, prime_eightyEightCH_1196537, prime_eightyEightCH_28449694799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820801 : Nat.totient 104039485801048370740999820801 = 101901040471411352605698361344 := by
  rw [← show ((([(53, 1), (983, 1), (1973, 1), (5119, 1), (197722728467580577, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_53, prime_eightyEightCH_983, prime_eightyEightCH_1973, prime_eightyEightCH_5119, prime_eightyEightCH_197722728467580577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820802 : Nat.totient 104039485801048370740999820802 = 31527116179024535088684857280 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (44020219, 1), (2661788359, 1), (13453291157, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_11, prime_eightyEightCH_44020219, prime_eightyEightCH_2661788359, prime_eightyEightCH_13453291157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820803 : Nat.totient 104039485801048370740999820803 = 103894785542632448111318318248 := by
  rw [← show ((([(719, 1), (144700258415922629681501837, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_719, prime_eightyEightCH_144700258415922629681501837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820804 : Nat.totient 104039485801048370740999820804 = 48954325897314228055834897920 := by
  rw [← show ((([(2, 2), (17, 1), (9013, 1), (169753959641707681618381, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_17, prime_eightyEightCH_9013, prime_eightyEightCH_169753959641707681618381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820805 : Nat.totient 104039485801048370740999820805 = 55487724194498222973779649216 := by
  rw [← show ((([(3, 3), (5, 1), (35431397, 1), (21750845945632442519, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_35431397, prime_eightyEightCH_21750845945632442519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820806 : Nat.totient 104039485801048370740999820806 = 51732341006046151197182231160 := by
  rw [← show ((([(2, 1), (181, 1), (287401894478034173317679063, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_181, prime_eightyEightCH_287401894478034173317679063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820807 : Nat.totient 104039485801048370740999820807 = 82232147877892112933273145600 := by
  rw [← show ((([(7, 1), (13, 1), (971, 1), (2532007, 1), (465021114700019641, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_7, prime_eightyEightCH_13, prime_eightyEightCH_971, prime_eightyEightCH_2532007, prime_eightyEightCH_465021114700019641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820808 : Nat.totient 104039485801048370740999820808 = 33327079931175512374028795904 := by
  rw [← show ((([(2, 3), (3, 1), (29, 1), (229, 1), (3167, 1), (251233, 1), (2230549, 1), (367804433, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_29, prime_eightyEightCH_229, prime_eightyEightCH_3167, prime_eightyEightCH_251233, prime_eightyEightCH_2230549, prime_eightyEightCH_367804433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820809 : Nat.totient 104039485801048370740999820809 = 98563723389360272472589179216 := by
  rw [← show ((([(19, 1), (89068691917, 1), (61477970459969983, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_19, prime_eightyEightCH_89068691917, prime_eightyEightCH_61477970459969983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820810 : Nat.totient 104039485801048370740999820810 = 41614794158855523551890606080 := by
  rw [← show ((([(2, 1), (5, 1), (41611, 1), (897914497, 1), (278455025774243, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_41611, prime_eightyEightCH_897914497, prime_eightyEightCH_278455025774243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820811 : Nat.totient 104039485801048370740999820811 = 65308133996049113951224320000 := by
  rw [← show ((([(3, 1), (31, 1), (37, 1), (899406721, 1), (33616879380657851, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_31, prime_eightyEightCH_37, prime_eightyEightCH_899406721, prime_eightyEightCH_33616879380657851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820812 : Nat.totient 104039485801048370740999820812 = 51951144679912742671231995456 := by
  rw [← show ((([(2, 2), (1063, 1), (2663, 1), (566047, 1), (965227, 1), (16817127623, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_1063, prime_eightyEightCH_2663, prime_eightyEightCH_566047, prime_eightyEightCH_965227, prime_eightyEightCH_16817127623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820813 : Nat.totient 104039485801048370740999820813 = 94581327767346190222873684480 := by
  rw [← show ((([(11, 1), (4119239, 1), (2296087960135981223297, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_11, prime_eightyEightCH_4119239, prime_eightyEightCH_2296087960135981223297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820814 : Nat.totient 104039485801048370740999820814 = 29721736120113395960545812672 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (7759, 1), (207029029, 1), (514032590558699, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_7, prime_eightyEightCH_7759, prime_eightyEightCH_207029029, prime_eightyEightCH_514032590558699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820815 : Nat.totient 104039485801048370740999820815 = 83231588640838696592799856648 := by
  rw [← show ((([(5, 1), (20807897160209674148199964163, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_20807897160209674148199964163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820816 : Nat.totient 104039485801048370740999820816 = 52013836264564094058433245216 := by
  rw [← show ((([(2, 4), (8807, 1), (738329495011414008324343, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_8807, prime_eightyEightCH_738329495011414008324343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820817 : Nat.totient 104039485801048370740999820817 = 68528646415826855213761377792 := by
  rw [← show ((([(3, 1), (109, 1), (353, 1), (901313215696375936628807, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_109, prime_eightyEightCH_353, prime_eightyEightCH_901313215696375936628807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820818 : Nat.totient 104039485801048370740999820818 = 52018983643270975207441017520 := by
  rw [← show ((([(2, 1), (68543, 1), (161871173, 1), (4688517904326731, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_68543, prime_eightyEightCH_161871173, prime_eightyEightCH_4688517904326731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820819 : Nat.totient 104039485801048370740999820819 = 101398114146156152605194339360 := by
  rw [← show ((([(79, 1), (103, 1), (311, 1), (5263003, 1), (7811597801204839, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_79, prime_eightyEightCH_103, prime_eightyEightCH_311, prime_eightyEightCH_5263003, prime_eightyEightCH_7811597801204839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820820 : Nat.totient 104039485801048370740999820820 = 24464398807334384225518878720 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (769, 1), (1241115061, 1), (6076274325917, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_13, prime_eightyEightCH_23, prime_eightyEightCH_769, prime_eightyEightCH_1241115061, prime_eightyEightCH_6076274325917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820821 : Nat.totient 104039485801048370740999820821 = 83931013755467593202823384768 := by
  rw [← show ((([(7, 1), (17, 1), (874281393286120762529410259, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_7, prime_eightyEightCH_17, prime_eightyEightCH_874281393286120762529410259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820822 : Nat.totient 104039485801048370740999820822 = 51705767297656997902574828928 := by
  rw [← show ((([(2, 1), (167, 1), (20849, 1), (9322636459, 1), (1602609644263, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_167, prime_eightyEightCH_20849, prime_eightyEightCH_9322636459, prime_eightyEightCH_1602609644263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820823 : Nat.totient 104039485801048370740999820823 = 68628269092564315118586470400 := by
  rw [← show ((([(3, 2), (97, 1), (4201, 1), (2166719263, 1), (13092682233977, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_97, prime_eightyEightCH_4201, prime_eightyEightCH_2166719263, prime_eightyEightCH_13092682233977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820824 : Nat.totient 104039485801048370740999820824 = 47290675341394633041372309120 := by
  rw [← show ((([(2, 3), (11, 1), (2081614957, 1), (567956566668166189, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_11, prime_eightyEightCH_2081614957, prime_eightyEightCH_567956566668166189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820825 : Nat.totient 104039485801048370740999820825 = 81652873720389836757659352000 := by
  rw [← show ((([(5, 2), (59, 1), (487, 1), (144836231233840351847701, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_59, prime_eightyEightCH_487, prime_eightyEightCH_144836231233840351847701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820826 : Nat.totient 104039485801048370740999820826 = 34679756198511843368824694400 := by
  rw [← show ((([(2, 1), (3, 1), (478991, 1), (36200918806772420477281, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_478991, prime_eightyEightCH_36200918806772420477281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820827 : Nat.totient 104039485801048370740999820827 = 101367771205078099874227682592 := by
  rw [← show ((([(47, 1), (223, 1), (68023, 1), (145928357578959846029, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_47, prime_eightyEightCH_223, prime_eightyEightCH_68023, prime_eightyEightCH_145928357578959846029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820828 : Nat.totient 104039485801048370740999820828 = 41211107964465918209097292800 := by
  rw [← show ((([(2, 2), (7, 2), (19, 1), (41, 1), (201211, 1), (314146013, 1), (10780065419, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_7, prime_eightyEightCH_19, prime_eightyEightCH_41, prime_eightyEightCH_201211, prime_eightyEightCH_314146013, prime_eightyEightCH_10780065419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820829 : Nat.totient 104039485801048370740999820829 = 68186362669467186072585888000 := by
  rw [← show ((([(3, 1), (67, 1), (853, 1), (1181, 1), (355951, 1), (1443487387324603, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_67, prime_eightyEightCH_853, prime_eightyEightCH_1181, prime_eightyEightCH_355951, prime_eightyEightCH_1443487387324603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820830 : Nat.totient 104039485801048370740999820830 = 41547234527469728282732051232 := by
  rw [← show ((([(2, 1), (5, 1), (607, 1), (17139948237405003416968669, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_607, prime_eightyEightCH_17139948237405003416968669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820831 : Nat.totient 104039485801048370740999820831 = 103350482481604860569751112800 := by
  rw [← show ((([(151, 1), (1011078853, 1), (681453494137599077, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_151, prime_eightyEightCH_1011078853, prime_eightyEightCH_681453494137599077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820832 : Nat.totient 104039485801048370740999820832 = 34678123476770823804066373632 := by
  rw [← show ((([(2, 5), (3, 4), (36209, 1), (52639, 1), (391627, 1), (53773265773, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_36209, prime_eightyEightCH_52639, prime_eightyEightCH_391627, prime_eightyEightCH_53773265773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820833 : Nat.totient 104039485801048370740999820833 = 96036448431736957607076757680 := by
  rw [← show ((([(13, 1), (8003037369311413133923063141, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_13, prime_eightyEightCH_8003037369311413133923063141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820834 : Nat.totient 104039485801048370740999820834 = 52012510821959630819201194848 := by
  rw [← show ((([(2, 1), (7193, 1), (625404643, 1), (11563705961128883, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_7193, prime_eightyEightCH_625404643, prime_eightyEightCH_11563705961128883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820835 : Nat.totient 104039485801048370740999820835 = 43237188729759112870504366080 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (11, 1), (247674433, 1), (363693078017562529, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_7, prime_eightyEightCH_11, prime_eightyEightCH_247674433, prime_eightyEightCH_363693078017562529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820836 : Nat.totient 104039485801048370740999820836 = 51744189643187072933571310080 := by
  rw [← show ((([(2, 2), (191, 1), (16369, 1), (1388053, 1), (5993446606802507, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_191, prime_eightyEightCH_16369, prime_eightyEightCH_1388053, prime_eightyEightCH_5993446606802507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820837 : Nat.totient 104039485801048370740999820837 = 99812096195690595957980935104 := by
  rw [← show ((([(29, 1), (157, 1), (22850754623555539367669629, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_29, prime_eightyEightCH_157, prime_eightyEightCH_22850754623555539367669629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820838 : Nat.totient 104039485801048370740999820838 = 32428821101367861208105689600 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (199, 1), (691, 1), (7417659635615178324941, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_17, prime_eightyEightCH_199, prime_eightyEightCH_691, prime_eightyEightCH_7417659635615178324941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820839 : Nat.totient 104039485801048370740999820839 = 104039485801048370740999820838 := by
  rw [← show ((([(104039485801048370740999820839, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_104039485801048370740999820839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820840 : Nat.totient 104039485801048370740999820840 = 40560192502836717269065199616 := by
  rw [← show ((([(2, 3), (5, 1), (43, 1), (463, 1), (1776980273, 1), (73520110754653, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_43, prime_eightyEightCH_463, prime_eightyEightCH_1776980273, prime_eightyEightCH_73520110754653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820841 : Nat.totient 104039485801048370740999820841 = 69272631281164195083712389120 := by
  rw [← show ((([(3, 2), (797, 1), (82630661077, 1), (175531934437121, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_797, prime_eightyEightCH_82630661077, prime_eightyEightCH_175531934437121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820842 : Nat.totient 104039485801048370740999820842 = 43142287770875735997541632000 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (6229, 1), (53881, 1), (31021517, 1), (23024566261, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_7, prime_eightyEightCH_31, prime_eightyEightCH_6229, prime_eightyEightCH_53881, prime_eightyEightCH_31021517, prime_eightyEightCH_23024566261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820843 : Nat.totient 104039485801048370740999820843 = 99515653849352822441618484864 := by
  rw [← show ((([(23, 1), (264637, 1), (17093059188221629717393, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_23, prime_eightyEightCH_264637, prime_eightyEightCH_17093059188221629717393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820844 : Nat.totient 104039485801048370740999820844 = 34679713121436563791203894336 := by
  rw [← show ((([(2, 2), (3, 1), (300317, 1), (23477448899, 1), (1229663069839, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_300317, prime_eightyEightCH_23477448899, prime_eightyEightCH_1229663069839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820845 : Nat.totient 104039485801048370740999820845 = 81973443451513551091047387648 := by
  rw [← show ((([(5, 1), (127, 1), (137, 1), (2545357, 1), (469845640492965883, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_127, prime_eightyEightCH_137, prime_eightyEightCH_2545357, prime_eightyEightCH_469845640492965883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820846 : Nat.totient 104039485801048370740999820846 = 43649381990496589974935424000 := by
  rw [← show ((([(2, 1), (11, 1), (13, 1), (12301, 1), (113503609, 1), (260544598953029, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_11, prime_eightyEightCH_13, prime_eightyEightCH_12301, prime_eightyEightCH_113503609, prime_eightyEightCH_260544598953029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820847 : Nat.totient 104039485801048370740999820847 = 65709057377765852171124496704 := by
  rw [← show ((([(3, 1), (19, 2), (780397, 1), (8940539, 1), (13768621054723, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_19, prime_eightyEightCH_780397, prime_eightyEightCH_8940539, prime_eightyEightCH_13768621054723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820848 : Nat.totient 104039485801048370740999820848 = 50613395500118231122639576320 := by
  rw [← show ((([(2, 4), (37, 1), (123931, 1), (1418066300311730387749, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_37, prime_eightyEightCH_123931, prime_eightyEightCH_1418066300311730387749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820849 : Nat.totient 104039485801048370740999820849 = 89176699904145965921992162896 := by
  rw [← show ((([(7, 1), (40332499, 1), (368506391975960948093, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_7, prime_eightyEightCH_40332499, prime_eightyEightCH_368506391975960948093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820850 : Nat.totient 104039485801048370740999820850 = 27700254153689355402709248000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (881, 1), (2287, 1), (569943811, 1), (201331425389, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_881, prime_eightyEightCH_2287, prime_eightyEightCH_569943811, prime_eightyEightCH_201331425389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820851 : Nat.totient 104039485801048370740999820851 = 104034712645977300475714456008 := by
  rw [← show ((([(26647, 1), (119747, 1), (32605077230948625239, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_26647, prime_eightyEightCH_119747, prime_eightyEightCH_32605077230948625239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820852 : Nat.totient 104039485801048370740999820852 = 52012040202493935093153792000 := by
  rw [← show ((([(2, 2), (10837, 1), (17921, 1), (1232236769, 1), (108685780601, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_10837, prime_eightyEightCH_17921, prime_eightyEightCH_1232236769, prime_eightyEightCH_108685780601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820853 : Nat.totient 104039485801048370740999820853 = 69348749879233164666486003008 := by
  rw [← show ((([(3, 1), (6359, 1), (5453660732874580423599089, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_6359, prime_eightyEightCH_5453660732874580423599089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820854 : Nat.totient 104039485801048370740999820854 = 50999068372503787219641589632 := by
  rw [← show ((([(2, 1), (53, 1), (1303, 1), (332247997, 1), (2267177613866749, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_53, prime_eightyEightCH_1303, prime_eightyEightCH_332247997, prime_eightyEightCH_2267177613866749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820855 : Nat.totient 104039485801048370740999820855 = 78335609692593997465294367232 := by
  rw [← show ((([(5, 1), (17, 1), (25487599, 1), (1110328279, 1), (43251278003, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_17, prime_eightyEightCH_25487599, prime_eightyEightCH_1110328279, prime_eightyEightCH_43251278003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820856 : Nat.totient 104039485801048370740999820856 = 29667167435246499902499886080 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (509, 1), (50881791161, 1), (23911605771583, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_7, prime_eightyEightCH_509, prime_eightyEightCH_50881791161, prime_eightyEightCH_23911605771583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820857 : Nat.totient 104039485801048370740999820857 = 94581314026010951175377151360 := by
  rw [← show ((([(11, 1), (2576993, 1), (3670221484040732418859, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_11, prime_eightyEightCH_2576993, prime_eightyEightCH_3670221484040732418859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820858 : Nat.totient 104039485801048370740999820858 = 51166960140054028719285789360 := by
  rw [← show ((([(2, 1), (61, 1), (568712867, 1), (1499496002260129067, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_61, prime_eightyEightCH_568712867, prime_eightyEightCH_1499496002260129067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820859 : Nat.totient 104039485801048370740999820859 = 64024076804543638873598509056 := by
  rw [← show ((([(3, 3), (13, 1), (288817, 1), (135586133, 1), (7569253555169, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_13, prime_eightyEightCH_288817, prime_eightyEightCH_135586133, prime_eightyEightCH_7569253555169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820860 : Nat.totient 104039485801048370740999820860 = 41615155855164617253995202560 := by
  rw [← show ((([(2, 2), (5, 1), (104891, 1), (172169, 1), (288054735061348817, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_104891, prime_eightyEightCH_172169, prime_eightyEightCH_288054735061348817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820861 : Nat.totient 104039485801048370740999820861 = 104039485800920418481620313824 := by
  rw [← show ((([(813116919269, 1), (127951446262587769, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_813116919269, prime_eightyEightCH_127951446262587769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820862 : Nat.totient 104039485801048370740999820862 = 34415097084316254952493579160 := by
  rw [← show ((([(2, 1), (3, 1), (131, 1), (132365758016600980586513767, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_131, prime_eightyEightCH_132365758016600980586513767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820863 : Nat.totient 104039485801048370740999820863 = 87870537809680023238181705280 := by
  rw [← show ((([(7, 1), (71, 1), (1753, 1), (119415277519134626057543, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_7, prime_eightyEightCH_71, prime_eightyEightCH_1753, prime_eightyEightCH_119415277519134626057543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820864 : Nat.totient 104039485801048370740999820864 = 51307133016954474275383443456 := by
  rw [← show ((([(2, 6), (73, 1), (5338427, 1), (48667169, 1), (85712856899, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_73, prime_eightyEightCH_5338427, prime_eightyEightCH_48667169, prime_eightyEightCH_85712856899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820865 : Nat.totient 104039485801048370740999820865 = 55166987285865246649505303040 := by
  rw [← show ((([(3, 1), (5, 1), (173, 1), (314341987, 1), (127543532386107641, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_173, prime_eightyEightCH_314341987, prime_eightyEightCH_127543532386107641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820866 : Nat.totient 104039485801048370740999820866 = 45512156056732979272159463424 := by
  rw [← show ((([(2, 1), (19, 1), (23, 1), (29, 1), (31649, 1), (510047, 1), (254283732002207, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_19, prime_eightyEightCH_23, prime_eightyEightCH_29, prime_eightyEightCH_31649, prime_eightyEightCH_510047, prime_eightyEightCH_254283732002207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820867 : Nat.totient 104039485801048370740999820867 = 104033847625902232575403991040 := by
  rw [← show ((([(20903, 1), (157793, 1), (64476833, 1), (489213176581, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_20903, prime_eightyEightCH_157793, prime_eightyEightCH_64476833, prime_eightyEightCH_489213176581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820868 : Nat.totient 104039485801048370740999820868 = 31409872118106034330273305600 := by
  rw [← show ((([(2, 2), (3, 2), (11, 1), (269, 1), (740461, 1), (26324773, 1), (50105327719, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_11, prime_eightyEightCH_269, prime_eightyEightCH_740461, prime_eightyEightCH_26324773, prime_eightyEightCH_50105327719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820869 : Nat.totient 104039485801048370740999820869 = 101501828952408758756163715200 := by
  rw [← show ((([(41, 1), (1186693, 1), (4436071, 1), (482033777210303, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_41, prime_eightyEightCH_1186693, prime_eightyEightCH_4436071, prime_eightyEightCH_482033777210303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820870 : Nat.totient 104039485801048370740999820870 = 35670680846073727111199938560 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1486278368586405296299997441, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_7, prime_eightyEightCH_1486278368586405296299997441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820871 : Nat.totient 104039485801048370740999820871 = 69352542660007489177232944832 := by
  rw [← show ((([(3, 1), (9749, 1), (3557270345712325050124793, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_9749, prime_eightyEightCH_3557270345712325050124793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820872 : Nat.totient 104039485801048370740999820872 = 45010036761487970774294384640 := by
  rw [← show ((([(2, 3), (13, 2), (17, 1), (271, 1), (2677, 1), (6239573746146407299, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_13, prime_eightyEightCH_17, prime_eightyEightCH_271, prime_eightyEightCH_2677, prime_eightyEightCH_6239573746146407299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820873 : Nat.totient 104039485801048370740999820873 = 100683373355172488377137648240 := by
  rw [← show ((([(31, 1), (147896488757, 1), (22692306446229019, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_31, prime_eightyEightCH_147896488757, prime_eightyEightCH_22692306446229019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820874 : Nat.totient 104039485801048370740999820874 = 33900066766557613836454216704 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (823, 1), (67577, 1), (226409, 1), (29299260503663, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_47, prime_eightyEightCH_823, prime_eightyEightCH_67577, prime_eightyEightCH_226409, prime_eightyEightCH_29299260503663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820875 : Nat.totient 104039485801048370740999820875 = 82874371522208487594547473600 := by
  rw [← show ((([(5, 3), (233, 1), (3572171186302089982523599, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_233, prime_eightyEightCH_3572171186302089982523599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820876 : Nat.totient 104039485801048370740999820876 = 52019742900510855899634630288 := by
  rw [← show ((([(2, 2), (3904899144253, 1), (6660830533495823, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3904899144253, prime_eightyEightCH_6660830533495823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820877 : Nat.totient 104039485801048370740999820877 = 59451076463800821399021139200 := by
  rw [← show ((([(3, 2), (7, 2), (1020101, 1), (231268473771637784497, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_7, prime_eightyEightCH_1020101, prime_eightyEightCH_231268473771637784497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820878 : Nat.totient 104039485801048370740999820878 = 52016576178487262975335195656 := by
  rw [← show ((([(2, 1), (16427, 1), (3166722036922395164698357, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_16427, prime_eightyEightCH_3166722036922395164698357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820879 : Nat.totient 104039485801048370740999820879 = 93440651838471909647455359360 := by
  rw [← show ((([(11, 1), (83, 1), (80239, 1), (1420175159365398756497, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_11, prime_eightyEightCH_83, prime_eightyEightCH_80239, prime_eightyEightCH_1420175159365398756497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820880 : Nat.totient 104039485801048370740999820880 = 27743862880279565530933285504 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (433497857504368211420832587, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_433497857504368211420832587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820881 : Nat.totient 104039485801048370740999820881 = 102873308097297965154943468800 := by
  rw [← show ((([(101, 1), (1237, 1), (1949, 1), (197953619, 1), (2158399534223, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_101, prime_eightyEightCH_1237, prime_eightyEightCH_1949, prime_eightyEightCH_197953619, prime_eightyEightCH_2158399534223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820882 : Nat.totient 104039485801048370740999820882 = 50954548122909624888186583168 := by
  rw [← show ((([(2, 1), (89, 1), (107, 1), (304377459143, 1), (17946589526069, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_89, prime_eightyEightCH_107, prime_eightyEightCH_304377459143, prime_eightyEightCH_17946589526069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820883 : Nat.totient 104039485801048370740999820883 = 67745221657552698477970348800 := by
  rw [← show ((([(3, 1), (43, 1), (47701, 1), (2806067503, 1), (6025358458409, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_43, prime_eightyEightCH_47701, prime_eightyEightCH_2806067503, prime_eightyEightCH_6025358458409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820884 : Nat.totient 104039485801048370740999820884 = 43830893245974052648002412896 := by
  rw [← show ((([(2, 2), (7, 1), (59, 1), (25439, 1), (2475643577734982680903, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_7, prime_eightyEightCH_59, prime_eightyEightCH_25439, prime_eightyEightCH_2475643577734982680903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820885 : Nat.totient 104039485801048370740999820885 = 70818342556601419918305315840 := by
  rw [← show ((([(5, 1), (13, 1), (19, 1), (37, 1), (1001280653, 1), (2273912194670231, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_5, prime_eightyEightCH_13, prime_eightyEightCH_19, prime_eightyEightCH_37, prime_eightyEightCH_1001280653, prime_eightyEightCH_2273912194670231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820886 : Nat.totient 104039485801048370740999820886 = 34679823030058779239947584768 := by
  rw [← show ((([(2, 1), (3, 3), (6290827, 1), (603537953, 1), (507448659539, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_6290827, prime_eightyEightCH_603537953, prime_eightyEightCH_507448659539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820887 : Nat.totient 104039485801048370740999820887 = 104039485801048370740999820886 := by
  rw [← show ((([(104039485801048370740999820887, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_104039485801048370740999820887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820888 : Nat.totient 104039485801048370740999820888 = 52010583578819653639308780960 := by
  rw [← show ((([(2, 3), (5783, 1), (317071, 1), (7092486134968332227, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5783, prime_eightyEightCH_317071, prime_eightyEightCH_7092486134968332227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820889 : Nat.totient 104039485801048370740999820889 = 62404635337461242667753562112 := by
  rw [← show ((([(3, 1), (17, 1), (23, 1), (1697, 1), (52265889105265432926869, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_17, prime_eightyEightCH_23, prime_eightyEightCH_1697, prime_eightyEightCH_52265889105265432926869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820890 : Nat.totient 104039485801048370740999820890 = 37802490616714232187790483200 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (1259, 1), (751241864402111132507761, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_11, prime_eightyEightCH_1259, prime_eightyEightCH_751241864402111132507761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820891 : Nat.totient 104039485801048370740999820891 = 89175135409205988884059138560 := by
  rw [← show ((([(7, 1), (56921, 1), (2869672217, 1), (90990351502109, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_7, prime_eightyEightCH_56921, prime_eightyEightCH_2869672217, prime_eightyEightCH_90990351502109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820892 : Nat.totient 104039485801048370740999820892 = 34500140035085017207528611840 := by
  rw [← show ((([(2, 2), (3, 1), (193, 1), (103239881, 1), (435123106858999477, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_193, prime_eightyEightCH_103239881, prime_eightyEightCH_435123106858999477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820893 : Nat.totient 104039485801048370740999820893 = 103887533129132482237280256000 := by
  rw [← show ((([(761, 1), (13291, 1), (14081, 1), (2439197, 1), (299485297499, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_761, prime_eightyEightCH_13291, prime_eightyEightCH_14081, prime_eightyEightCH_2439197, prime_eightyEightCH_299485297499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820894 : Nat.totient 104039485801048370740999820894 = 52019742900524185370499910446 := by
  rw [← show ((([(2, 1), (52019742900524185370499910447, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_52019742900524185370499910447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820895 : Nat.totient 104039485801048370740999820895 = 53574355889200694283531694080 := by
  rw [← show ((([(3, 2), (5, 1), (29, 1), (3053356919, 1), (26110194786844481, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_5, prime_eightyEightCH_29, prime_eightyEightCH_3053356919, prime_eightyEightCH_26110194786844481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820896 : Nat.totient 104039485801048370740999820896 = 51243328810241766167493617280 := by
  rw [← show ((([(2, 5), (67, 1), (2989646411, 1), (16231310630193619, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_67, prime_eightyEightCH_2989646411, prime_eightyEightCH_16231310630193619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820897 : Nat.totient 104039485801048370740999820897 = 104039485799783342729213362176 := by
  rw [← show ((([(82242836993, 1), (1265027929543621729, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_82242836993, prime_eightyEightCH_1265027929543621729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820898 : Nat.totient 104039485801048370740999820898 = 27091281383337266863024188672 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13, 1), (79, 1), (72253, 1), (33382786049290035899, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_3, prime_eightyEightCH_7, prime_eightyEightCH_13, prime_eightyEightCH_79, prime_eightyEightCH_72253, prime_eightyEightCH_33382786049290035899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820899 : Nat.totient 104039485801048370740999820899 = 104039485801047677640048403320 := by
  rw [← show ((([(219831312150391, 1), (473269639267189, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_219831312150391, prime_eightyEightCH_473269639267189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820900 : Nat.totient 104039485801048370740999820900 = 41615793557987772397569609600 := by
  rw [← show ((([(2, 2), (5, 2), (54582989, 1), (19060789397416174981, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_2, prime_eightyEightCH_5, prime_eightyEightCH_54582989, prime_eightyEightCH_19060789397416174981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyEightCH_104039485801048370740999820901 : Nat.totient 104039485801048370740999820901 = 63054233818817194388484739920 := by
  rw [← show ((([(3, 1), (11, 1), (3152711690940859719424236997, 1)] : List FactorBlock).map factorBlockValue).prod) = 104039485801048370740999820901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyEightCH_3, prime_eightyEightCH_11, prime_eightyEightCH_3152711690940859719424236997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyEightCH : certifiedKill 1 104039485801048370740999820799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyEightCH_104039485801048370740999820800, phi_eightyEightCH_104039485801048370740999820801, phi_eightyEightCH_104039485801048370740999820802,
    phi_eightyEightCH_104039485801048370740999820803, phi_eightyEightCH_104039485801048370740999820804, phi_eightyEightCH_104039485801048370740999820805,
    phi_eightyEightCH_104039485801048370740999820806, phi_eightyEightCH_104039485801048370740999820807, phi_eightyEightCH_104039485801048370740999820808,
    phi_eightyEightCH_104039485801048370740999820809, phi_eightyEightCH_104039485801048370740999820810, phi_eightyEightCH_104039485801048370740999820811,
    phi_eightyEightCH_104039485801048370740999820812, phi_eightyEightCH_104039485801048370740999820813, phi_eightyEightCH_104039485801048370740999820814,
    phi_eightyEightCH_104039485801048370740999820815, phi_eightyEightCH_104039485801048370740999820816, phi_eightyEightCH_104039485801048370740999820817,
    phi_eightyEightCH_104039485801048370740999820818, phi_eightyEightCH_104039485801048370740999820819, phi_eightyEightCH_104039485801048370740999820820,
    phi_eightyEightCH_104039485801048370740999820821, phi_eightyEightCH_104039485801048370740999820822, phi_eightyEightCH_104039485801048370740999820823,
    phi_eightyEightCH_104039485801048370740999820824, phi_eightyEightCH_104039485801048370740999820825, phi_eightyEightCH_104039485801048370740999820826,
    phi_eightyEightCH_104039485801048370740999820827, phi_eightyEightCH_104039485801048370740999820828, phi_eightyEightCH_104039485801048370740999820829,
    phi_eightyEightCH_104039485801048370740999820830, phi_eightyEightCH_104039485801048370740999820831, phi_eightyEightCH_104039485801048370740999820832,
    phi_eightyEightCH_104039485801048370740999820833, phi_eightyEightCH_104039485801048370740999820834, phi_eightyEightCH_104039485801048370740999820835,
    phi_eightyEightCH_104039485801048370740999820836, phi_eightyEightCH_104039485801048370740999820837, phi_eightyEightCH_104039485801048370740999820838,
    phi_eightyEightCH_104039485801048370740999820839, phi_eightyEightCH_104039485801048370740999820840, phi_eightyEightCH_104039485801048370740999820841,
    phi_eightyEightCH_104039485801048370740999820842, phi_eightyEightCH_104039485801048370740999820843, phi_eightyEightCH_104039485801048370740999820844,
    phi_eightyEightCH_104039485801048370740999820845, phi_eightyEightCH_104039485801048370740999820846, phi_eightyEightCH_104039485801048370740999820847,
    phi_eightyEightCH_104039485801048370740999820848, phi_eightyEightCH_104039485801048370740999820849, phi_eightyEightCH_104039485801048370740999820850,
    phi_eightyEightCH_104039485801048370740999820851, phi_eightyEightCH_104039485801048370740999820852, phi_eightyEightCH_104039485801048370740999820853,
    phi_eightyEightCH_104039485801048370740999820854, phi_eightyEightCH_104039485801048370740999820855, phi_eightyEightCH_104039485801048370740999820856,
    phi_eightyEightCH_104039485801048370740999820857, phi_eightyEightCH_104039485801048370740999820858, phi_eightyEightCH_104039485801048370740999820859,
    phi_eightyEightCH_104039485801048370740999820860, phi_eightyEightCH_104039485801048370740999820861, phi_eightyEightCH_104039485801048370740999820862,
    phi_eightyEightCH_104039485801048370740999820863, phi_eightyEightCH_104039485801048370740999820864, phi_eightyEightCH_104039485801048370740999820865,
    phi_eightyEightCH_104039485801048370740999820866, phi_eightyEightCH_104039485801048370740999820867, phi_eightyEightCH_104039485801048370740999820868,
    phi_eightyEightCH_104039485801048370740999820869, phi_eightyEightCH_104039485801048370740999820870, phi_eightyEightCH_104039485801048370740999820871,
    phi_eightyEightCH_104039485801048370740999820872, phi_eightyEightCH_104039485801048370740999820873, phi_eightyEightCH_104039485801048370740999820874,
    phi_eightyEightCH_104039485801048370740999820875, phi_eightyEightCH_104039485801048370740999820876, phi_eightyEightCH_104039485801048370740999820877,
    phi_eightyEightCH_104039485801048370740999820878, phi_eightyEightCH_104039485801048370740999820879, phi_eightyEightCH_104039485801048370740999820880,
    phi_eightyEightCH_104039485801048370740999820881, phi_eightyEightCH_104039485801048370740999820882, phi_eightyEightCH_104039485801048370740999820883,
    phi_eightyEightCH_104039485801048370740999820884, phi_eightyEightCH_104039485801048370740999820885, phi_eightyEightCH_104039485801048370740999820886,
    phi_eightyEightCH_104039485801048370740999820887, phi_eightyEightCH_104039485801048370740999820888, phi_eightyEightCH_104039485801048370740999820889,
    phi_eightyEightCH_104039485801048370740999820890, phi_eightyEightCH_104039485801048370740999820891, phi_eightyEightCH_104039485801048370740999820892,
    phi_eightyEightCH_104039485801048370740999820893, phi_eightyEightCH_104039485801048370740999820894, phi_eightyEightCH_104039485801048370740999820895,
    phi_eightyEightCH_104039485801048370740999820896, phi_eightyEightCH_104039485801048370740999820897, phi_eightyEightCH_104039485801048370740999820898,
    phi_eightyEightCH_104039485801048370740999820899, phi_eightyEightCH_104039485801048370740999820900, phi_eightyEightCH_104039485801048370740999820901
    ]

end TotientTailPeriodKiller
end Erdos249257
