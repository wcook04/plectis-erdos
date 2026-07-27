import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetySixCPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetySixCPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetySixCPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetySixCPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetySixCPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetySixCPFastPow a n * ninetySixCPFastPow a n * a else ninetySixCPFastPow a n * ninetySixCPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetySixCP_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetySixCP_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetySixCP_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetySixCP_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetySixCP_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetySixCP_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetySixCP_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetySixCP_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetySixCP_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetySixCP_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetySixCP_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetySixCP_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetySixCP_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetySixCP_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetySixCP_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetySixCP_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetySixCP_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetySixCP_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetySixCP_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetySixCP_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetySixCP_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetySixCP_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetySixCP_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetySixCP_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetySixCP_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetySixCP_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetySixCP_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetySixCP_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetySixCP_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetySixCP_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetySixCP_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetySixCP_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetySixCP_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetySixCP_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetySixCP_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetySixCP_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetySixCP_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetySixCP_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetySixCP_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetySixCP_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetySixCP_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetySixCP_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetySixCP_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetySixCP_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetySixCP_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetySixCP_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetySixCP_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetySixCP_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetySixCP_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetySixCP_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetySixCP_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetySixCP_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetySixCP_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetySixCP_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetySixCP_281 : Nat.Prime 281 := by norm_num

private theorem prime_ninetySixCP_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetySixCP_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetySixCP_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetySixCP_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetySixCP_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetySixCP_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetySixCP_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetySixCP_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetySixCP_353 : Nat.Prime 353 := by norm_num

private theorem prime_ninetySixCP_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetySixCP_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetySixCP_373 : Nat.Prime 373 := by norm_num

private theorem prime_ninetySixCP_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetySixCP_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetySixCP_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetySixCP_433 : Nat.Prime 433 := by norm_num

private theorem prime_ninetySixCP_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetySixCP_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetySixCP_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetySixCP_461 : Nat.Prime 461 := by norm_num

private theorem prime_ninetySixCP_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetySixCP_491 : Nat.Prime 491 := by norm_num

private theorem prime_ninetySixCP_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetySixCP_521 : Nat.Prime 521 := by norm_num

private theorem prime_ninetySixCP_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetySixCP_541 : Nat.Prime 541 := by norm_num

private theorem prime_ninetySixCP_547 : Nat.Prime 547 := by norm_num

private theorem prime_ninetySixCP_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetySixCP_587 : Nat.Prime 587 := by norm_num

private theorem prime_ninetySixCP_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetySixCP_601 : Nat.Prime 601 := by norm_num

private theorem prime_ninetySixCP_607 : Nat.Prime 607 := by norm_num

private theorem prime_ninetySixCP_613 : Nat.Prime 613 := by norm_num

private theorem prime_ninetySixCP_617 : Nat.Prime 617 := by norm_num

private theorem prime_ninetySixCP_619 : Nat.Prime 619 := by norm_num

private theorem prime_ninetySixCP_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetySixCP_641 : Nat.Prime 641 := by norm_num

private theorem prime_ninetySixCP_647 : Nat.Prime 647 := by norm_num

private theorem prime_ninetySixCP_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetySixCP_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetySixCP_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetySixCP_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetySixCP_719 : Nat.Prime 719 := by norm_num

private theorem prime_ninetySixCP_727 : Nat.Prime 727 := by norm_num

private theorem prime_ninetySixCP_757 : Nat.Prime 757 := by norm_num

private theorem prime_ninetySixCP_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetySixCP_853 : Nat.Prime 853 := by norm_num

private theorem prime_ninetySixCP_857 : Nat.Prime 857 := by norm_num

private theorem prime_ninetySixCP_883 : Nat.Prime 883 := by norm_num

private theorem prime_ninetySixCP_887 : Nat.Prime 887 := by norm_num

private theorem prime_ninetySixCP_941 : Nat.Prime 941 := by norm_num

private theorem prime_ninetySixCP_953 : Nat.Prime 953 := by norm_num

private theorem prime_ninetySixCP_967 : Nat.Prime 967 := by norm_num

private theorem prime_ninetySixCP_997 : Nat.Prime 997 := by norm_num

private theorem prime_ninetySixCP_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_ninetySixCP_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_ninetySixCP_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_ninetySixCP_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_ninetySixCP_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_ninetySixCP_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetySixCP_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_ninetySixCP_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_ninetySixCP_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_ninetySixCP_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_ninetySixCP_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_ninetySixCP_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_ninetySixCP_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_ninetySixCP_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_ninetySixCP_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_ninetySixCP_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_ninetySixCP_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_ninetySixCP_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_ninetySixCP_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_ninetySixCP_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_ninetySixCP_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetySixCP_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_ninetySixCP_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_ninetySixCP_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_ninetySixCP_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_ninetySixCP_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_ninetySixCP_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_ninetySixCP_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_ninetySixCP_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_ninetySixCP_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_ninetySixCP_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_ninetySixCP_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_ninetySixCP_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_ninetySixCP_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_ninetySixCP_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_ninetySixCP_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_ninetySixCP_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_ninetySixCP_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_ninetySixCP_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_ninetySixCP_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_ninetySixCP_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_ninetySixCP_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_ninetySixCP_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_ninetySixCP_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_ninetySixCP_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_ninetySixCP_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_ninetySixCP_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_ninetySixCP_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_ninetySixCP_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_ninetySixCP_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_ninetySixCP_3919 : Nat.Prime 3919 := by norm_num

private theorem prime_ninetySixCP_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_ninetySixCP_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_ninetySixCP_4447 : Nat.Prime 4447 := by norm_num

private theorem prime_ninetySixCP_4483 : Nat.Prime 4483 := by norm_num

private theorem prime_ninetySixCP_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_ninetySixCP_4723 : Nat.Prime 4723 := by norm_num

private theorem prime_ninetySixCP_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_ninetySixCP_4877 : Nat.Prime 4877 := by norm_num

private theorem prime_ninetySixCP_5153 : Nat.Prime 5153 := by norm_num

private theorem prime_ninetySixCP_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_ninetySixCP_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_ninetySixCP_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_ninetySixCP_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_ninetySixCP_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_ninetySixCP_5857 : Nat.Prime 5857 := by norm_num

private theorem prime_ninetySixCP_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_ninetySixCP_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_ninetySixCP_6203 : Nat.Prime 6203 := by norm_num

private theorem prime_ninetySixCP_6373 : Nat.Prime 6373 := by norm_num

private theorem prime_ninetySixCP_6421 : Nat.Prime 6421 := by norm_num

private theorem prime_ninetySixCP_6581 : Nat.Prime 6581 := by norm_num

private theorem prime_ninetySixCP_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_ninetySixCP_6971 : Nat.Prime 6971 := by norm_num

private theorem prime_ninetySixCP_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_ninetySixCP_7237 : Nat.Prime 7237 := by norm_num

private theorem prime_ninetySixCP_7459 : Nat.Prime 7459 := by norm_num

private theorem prime_ninetySixCP_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_ninetySixCP_7873 : Nat.Prime 7873 := by norm_num

private theorem prime_ninetySixCP_7883 : Nat.Prime 7883 := by norm_num

private theorem prime_ninetySixCP_8629 : Nat.Prime 8629 := by norm_num

private theorem prime_ninetySixCP_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_ninetySixCP_8803 : Nat.Prime 8803 := by norm_num

private theorem prime_ninetySixCP_8821 : Nat.Prime 8821 := by norm_num

private theorem prime_ninetySixCP_9391 : Nat.Prime 9391 := by norm_num

private theorem prime_ninetySixCP_10069 : Nat.Prime 10069 := by norm_num

private theorem prime_ninetySixCP_10739 : Nat.Prime 10739 := by norm_num

private theorem prime_ninetySixCP_10847 : Nat.Prime 10847 := by norm_num

private theorem prime_ninetySixCP_11119 : Nat.Prime 11119 := by norm_num

private theorem prime_ninetySixCP_11159 : Nat.Prime 11159 := by norm_num

private theorem prime_ninetySixCP_11681 : Nat.Prime 11681 := by norm_num

private theorem prime_ninetySixCP_11953 : Nat.Prime 11953 := by norm_num

private theorem prime_ninetySixCP_12043 : Nat.Prime 12043 := by norm_num

private theorem prime_ninetySixCP_12203 : Nat.Prime 12203 := by norm_num

private theorem prime_ninetySixCP_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_ninetySixCP_12973 : Nat.Prime 12973 := by norm_num

private theorem prime_ninetySixCP_13487 : Nat.Prime 13487 := by norm_num

private theorem prime_ninetySixCP_13687 : Nat.Prime 13687 := by norm_num

private theorem prime_ninetySixCP_13799 : Nat.Prime 13799 := by norm_num

private theorem prime_ninetySixCP_14411 : Nat.Prime 14411 := by norm_num

private theorem prime_ninetySixCP_14431 : Nat.Prime 14431 := by norm_num

private theorem prime_ninetySixCP_14831 : Nat.Prime 14831 := by norm_num

private theorem prime_ninetySixCP_15031 : Nat.Prime 15031 := by norm_num

private theorem prime_ninetySixCP_15137 : Nat.Prime 15137 := by norm_num

private theorem prime_ninetySixCP_15541 : Nat.Prime 15541 := by norm_num

private theorem prime_ninetySixCP_15569 : Nat.Prime 15569 := by norm_num

private theorem prime_ninetySixCP_15671 : Nat.Prime 15671 := by norm_num

private theorem prime_ninetySixCP_16519 : Nat.Prime 16519 := by norm_num

private theorem prime_ninetySixCP_16603 : Nat.Prime 16603 := by norm_num

private theorem prime_ninetySixCP_18013 : Nat.Prime 18013 := by norm_num

private theorem prime_ninetySixCP_18049 : Nat.Prime 18049 := by norm_num

private theorem prime_ninetySixCP_19379 : Nat.Prime 19379 := by norm_num

private theorem prime_ninetySixCP_19603 : Nat.Prime 19603 := by norm_num

private theorem prime_ninetySixCP_20129 : Nat.Prime 20129 := by norm_num

private theorem prime_ninetySixCP_20173 : Nat.Prime 20173 := by norm_num

private theorem prime_ninetySixCP_20681 : Nat.Prime 20681 := by norm_num

private theorem prime_ninetySixCP_20789 : Nat.Prime 20789 := by norm_num

private theorem prime_ninetySixCP_21143 : Nat.Prime 21143 := by norm_num

private theorem prime_ninetySixCP_21499 : Nat.Prime 21499 := by norm_num

private theorem prime_ninetySixCP_21937 : Nat.Prime 21937 := by norm_num

private theorem prime_ninetySixCP_22643 : Nat.Prime 22643 := by norm_num

private theorem prime_ninetySixCP_23029 : Nat.Prime 23029 := by norm_num

private theorem prime_ninetySixCP_23459 : Nat.Prime 23459 := by norm_num

private theorem prime_ninetySixCP_24413 : Nat.Prime 24413 := by norm_num

private theorem prime_ninetySixCP_24697 : Nat.Prime 24697 := by norm_num

private theorem prime_ninetySixCP_24967 : Nat.Prime 24967 := by norm_num

private theorem prime_ninetySixCP_25453 : Nat.Prime 25453 := by norm_num

private theorem prime_ninetySixCP_26821 : Nat.Prime 26821 := by norm_num

private theorem prime_ninetySixCP_27361 : Nat.Prime 27361 := by norm_num

private theorem prime_ninetySixCP_28579 : Nat.Prime 28579 := by norm_num

private theorem prime_ninetySixCP_29303 : Nat.Prime 29303 := by norm_num

private theorem prime_ninetySixCP_31307 : Nat.Prime 31307 := by norm_num

private theorem prime_ninetySixCP_32237 : Nat.Prime 32237 := by norm_num

private theorem prime_ninetySixCP_33073 : Nat.Prime 33073 := by norm_num

private theorem prime_ninetySixCP_33493 : Nat.Prime 33493 := by norm_num

private theorem prime_ninetySixCP_33751 : Nat.Prime 33751 := by norm_num

private theorem prime_ninetySixCP_34337 : Nat.Prime 34337 := by norm_num

private theorem prime_ninetySixCP_34703 : Nat.Prime 34703 := by norm_num

private theorem prime_ninetySixCP_35569 : Nat.Prime 35569 := by norm_num

private theorem prime_ninetySixCP_35803 : Nat.Prime 35803 := by norm_num

private theorem prime_ninetySixCP_36793 : Nat.Prime 36793 := by norm_num

private theorem prime_ninetySixCP_36877 : Nat.Prime 36877 := by norm_num

private theorem prime_ninetySixCP_37511 : Nat.Prime 37511 := by norm_num

private theorem prime_ninetySixCP_38449 : Nat.Prime 38449 := by norm_num

private theorem prime_ninetySixCP_38933 : Nat.Prime 38933 := by norm_num

private theorem prime_ninetySixCP_41047 : Nat.Prime 41047 := by norm_num

private theorem prime_ninetySixCP_41131 : Nat.Prime 41131 := by norm_num

private theorem prime_ninetySixCP_43633 : Nat.Prime 43633 := by norm_num

private theorem prime_ninetySixCP_43711 : Nat.Prime 43711 := by norm_num

private theorem prime_ninetySixCP_44357 : Nat.Prime 44357 := by norm_num

private theorem prime_ninetySixCP_45137 : Nat.Prime 45137 := by norm_num

private theorem prime_ninetySixCP_48571 : Nat.Prime 48571 := by norm_num

private theorem prime_ninetySixCP_55897 : Nat.Prime 55897 := by norm_num

private theorem prime_ninetySixCP_57139 : Nat.Prime 57139 := by norm_num

private theorem prime_ninetySixCP_59771 : Nat.Prime 59771 := by norm_num

private theorem prime_ninetySixCP_61729 : Nat.Prime 61729 := by norm_num

private theorem prime_ninetySixCP_63689 : Nat.Prime 63689 := by norm_num

private theorem prime_ninetySixCP_63839 : Nat.Prime 63839 := by norm_num

private theorem prime_ninetySixCP_64283 : Nat.Prime 64283 := by norm_num

private theorem prime_ninetySixCP_68669 : Nat.Prime 68669 := by norm_num

private theorem prime_ninetySixCP_72379 : Nat.Prime 72379 := by norm_num

private theorem prime_ninetySixCP_73757 : Nat.Prime 73757 := by norm_num

private theorem prime_ninetySixCP_73823 : Nat.Prime 73823 := by norm_num

private theorem prime_ninetySixCP_76541 : Nat.Prime 76541 := by norm_num

private theorem prime_ninetySixCP_79393 : Nat.Prime 79393 := by norm_num

private theorem prime_ninetySixCP_79691 : Nat.Prime 79691 := by norm_num

private theorem prime_ninetySixCP_80909 : Nat.Prime 80909 := by norm_num

private theorem prime_ninetySixCP_81647 : Nat.Prime 81647 := by norm_num

private theorem prime_ninetySixCP_84229 : Nat.Prime 84229 := by norm_num

private theorem prime_ninetySixCP_85199 : Nat.Prime 85199 := by norm_num

private theorem prime_ninetySixCP_85243 : Nat.Prime 85243 := by norm_num

private theorem prime_ninetySixCP_86249 : Nat.Prime 86249 := by norm_num

private theorem prime_ninetySixCP_86461 : Nat.Prime 86461 := by norm_num

private theorem prime_ninetySixCP_88793 : Nat.Prime 88793 := by norm_num

private theorem prime_ninetySixCP_89363 : Nat.Prime 89363 := by norm_num

private theorem prime_ninetySixCP_90547 : Nat.Prime 90547 := by norm_num

private theorem prime_ninetySixCP_95819 : Nat.Prime 95819 := by norm_num

private theorem prime_ninetySixCP_97553 : Nat.Prime 97553 := by norm_num

private theorem prime_ninetySixCP_102367 : Nat.Prime 102367 := by norm_num

private theorem prime_ninetySixCP_102611 : Nat.Prime 102611 := by norm_num

private theorem prime_ninetySixCP_103889 : Nat.Prime 103889 := by norm_num

private theorem prime_ninetySixCP_109943 : Nat.Prime 109943 := by norm_num

private theorem prime_ninetySixCP_115249 : Nat.Prime 115249 := by norm_num

private theorem prime_ninetySixCP_116027 : Nat.Prime 116027 := by norm_num

private theorem prime_ninetySixCP_121453 : Nat.Prime 121453 := by norm_num

private theorem prime_ninetySixCP_127727 : Nat.Prime 127727 := by norm_num

private theorem prime_ninetySixCP_128923 : Nat.Prime 128923 := by norm_num

private theorem prime_ninetySixCP_132863 : Nat.Prime 132863 := by norm_num

private theorem prime_ninetySixCP_135799 : Nat.Prime 135799 := by norm_num

private theorem prime_ninetySixCP_140321 : Nat.Prime 140321 := by norm_num

private theorem prime_ninetySixCP_140827 : Nat.Prime 140827 := by norm_num

private theorem prime_ninetySixCP_144439 : Nat.Prime 144439 := by norm_num

private theorem prime_ninetySixCP_145283 : Nat.Prime 145283 := by norm_num

private theorem prime_ninetySixCP_148411 : Nat.Prime 148411 := by norm_num

private theorem prime_ninetySixCP_152783 : Nat.Prime 152783 := by norm_num

private theorem prime_ninetySixCP_156421 : Nat.Prime 156421 := by norm_num

private theorem prime_ninetySixCP_158551 : Nat.Prime 158551 := by norm_num

private theorem prime_ninetySixCP_163211 : Nat.Prime 163211 := by norm_num

private theorem prime_ninetySixCP_164449 : Nat.Prime 164449 := by norm_num

private theorem prime_ninetySixCP_169633 : Nat.Prime 169633 := by norm_num

private theorem prime_ninetySixCP_169667 : Nat.Prime 169667 := by norm_num

private theorem prime_ninetySixCP_170759 : Nat.Prime 170759 := by norm_num

private theorem prime_ninetySixCP_175433 : Nat.Prime 175433 := by norm_num

private theorem prime_ninetySixCP_194809 : Nat.Prime 194809 := by norm_num

private theorem prime_ninetySixCP_196477 : Nat.Prime 196477 := by norm_num

private theorem prime_ninetySixCP_197641 : Nat.Prime 197641 := by norm_num

private theorem prime_ninetySixCP_202471 : Nat.Prime 202471 := by norm_num

private theorem prime_ninetySixCP_221489 : Nat.Prime 221489 := by norm_num

private theorem prime_ninetySixCP_226871 : Nat.Prime 226871 := by norm_num

private theorem prime_ninetySixCP_241361 : Nat.Prime 241361 := by norm_num

private theorem prime_ninetySixCP_257437 : Nat.Prime 257437 := by norm_num

private theorem prime_ninetySixCP_277859 : Nat.Prime 277859 := by norm_num

private theorem prime_ninetySixCP_278591 : Nat.Prime 278591 := by norm_num

private theorem prime_ninetySixCP_287783 : Nat.Prime 287783 := by norm_num

private theorem prime_ninetySixCP_296347 : Nat.Prime 296347 := by norm_num

private theorem prime_ninetySixCP_309241 : Nat.Prime 309241 := by norm_num

private theorem prime_ninetySixCP_316223 : Nat.Prime 316223 := by norm_num

private theorem prime_ninetySixCP_322757 : Nat.Prime 322757 := by norm_num

private theorem prime_ninetySixCP_333631 : Nat.Prime 333631 := by norm_num

private theorem prime_ninetySixCP_347299 : Nat.Prime 347299 := by norm_num

private theorem prime_ninetySixCP_361321 : Nat.Prime 361321 := by norm_num

private theorem prime_ninetySixCP_376807 : Nat.Prime 376807 := by norm_num

private theorem prime_ninetySixCP_405529 : Nat.Prime 405529 := by norm_num

private theorem prime_ninetySixCP_407747 : Nat.Prime 407747 := by norm_num

private theorem prime_ninetySixCP_417997 : Nat.Prime 417997 := by norm_num

private theorem prime_ninetySixCP_422627 : Nat.Prime 422627 := by norm_num

private theorem prime_ninetySixCP_448769 : Nat.Prime 448769 := by norm_num

private theorem prime_ninetySixCP_491219 : Nat.Prime 491219 := by norm_num

private theorem prime_ninetySixCP_491983 : Nat.Prime 491983 := by norm_num

private theorem prime_ninetySixCP_493993 : Nat.Prime 493993 := by norm_num

private theorem prime_ninetySixCP_544177 : Nat.Prime 544177 := by norm_num

private theorem prime_ninetySixCP_556321 : Nat.Prime 556321 := by norm_num

private theorem prime_ninetySixCP_565613 : Nat.Prime 565613 := by norm_num

private theorem prime_ninetySixCP_637543 : Nat.Prime 637543 := by norm_num

private theorem prime_ninetySixCP_659783 : Nat.Prime 659783 := by norm_num

private theorem prime_ninetySixCP_663409 : Nat.Prime 663409 := by norm_num

private theorem prime_ninetySixCP_683461 : Nat.Prime 683461 := by norm_num

private theorem prime_ninetySixCP_731957 : Nat.Prime 731957 := by norm_num

private theorem prime_ninetySixCP_804197 : Nat.Prime 804197 := by norm_num

private theorem prime_ninetySixCP_820213 : Nat.Prime 820213 := by norm_num

private theorem prime_ninetySixCP_912871 : Nat.Prime 912871 := by norm_num

private theorem prime_ninetySixCP_1162367 : Nat.Prime 1162367 := by norm_num

private theorem prime_ninetySixCP_1170857 : Nat.Prime 1170857 := by norm_num

private theorem prime_ninetySixCP_1368013 : Nat.Prime 1368013 := by norm_num

private theorem prime_ninetySixCP_1460821 : Nat.Prime 1460821 := by norm_num

private theorem prime_ninetySixCP_1523069 : Nat.Prime 1523069 := by norm_num

private theorem prime_ninetySixCP_1575473 : Nat.Prime 1575473 := by norm_num

private theorem prime_ninetySixCP_1614629 : Nat.Prime 1614629 := by norm_num

private theorem prime_ninetySixCP_1669781 : Nat.Prime 1669781 := by norm_num

private theorem prime_ninetySixCP_1698947 : Nat.Prime 1698947 := by norm_num

private theorem prime_ninetySixCP_1778531 : Nat.Prime 1778531 := by norm_num

private theorem prime_ninetySixCP_1793479 : Nat.Prime 1793479 := by norm_num

private theorem prime_ninetySixCP_1915481 : Nat.Prime 1915481 := by norm_num

private theorem prime_ninetySixCP_2040653 : Nat.Prime 2040653 := by norm_num

private theorem prime_ninetySixCP_2120731 : Nat.Prime 2120731 := by norm_num

private theorem prime_ninetySixCP_2223269 : Nat.Prime 2223269 := by norm_num

private theorem prime_ninetySixCP_2263229 : Nat.Prime 2263229 := by norm_num

private theorem prime_ninetySixCP_2277139 : Nat.Prime 2277139 := by norm_num

private theorem prime_ninetySixCP_2277941 : Nat.Prime 2277941 := by norm_num

private theorem prime_ninetySixCP_2535887 : Nat.Prime 2535887 := by norm_num

private theorem prime_ninetySixCP_2541593 : Nat.Prime 2541593 := by norm_num

private theorem prime_ninetySixCP_2830871 : Nat.Prime 2830871 := by norm_num

private theorem prime_ninetySixCP_2924513 : Nat.Prime 2924513 := by norm_num

private theorem prime_ninetySixCP_2941319 : Nat.Prime 2941319 := by norm_num

private theorem prime_ninetySixCP_2955751 : Nat.Prime 2955751 := by norm_num

private theorem prime_ninetySixCP_2969167 : Nat.Prime 2969167 := by norm_num

private theorem prime_ninetySixCP_2990137 : Nat.Prime 2990137 := by norm_num

private theorem prime_ninetySixCP_3342263 : Nat.Prime 3342263 := by norm_num

private theorem prime_ninetySixCP_3809837 : Nat.Prime 3809837 := by norm_num

private theorem prime_ninetySixCP_4225073 : Nat.Prime 4225073 := by norm_num

private theorem prime_ninetySixCP_4350919 : Nat.Prime 4350919 := by norm_num

private theorem prime_ninetySixCP_4444339 : Nat.Prime 4444339 := by norm_num

private theorem prime_ninetySixCP_4674253 : Nat.Prime 4674253 := by norm_num

private theorem prime_ninetySixCP_4675859 : Nat.Prime 4675859 := by norm_num

private theorem prime_ninetySixCP_4882057 : Nat.Prime 4882057 := by norm_num

private theorem prime_ninetySixCP_5041573 : Nat.Prime 5041573 := by norm_num

private theorem prime_ninetySixCP_5232553 : Nat.Prime 5232553 := by norm_num

private theorem prime_ninetySixCP_5516501 : Nat.Prime 5516501 := by norm_num

private theorem prime_ninetySixCP_5552201 : Nat.Prime 5552201 := by norm_num

private theorem prime_ninetySixCP_5630591 : Nat.Prime 5630591 := by norm_num

private theorem prime_ninetySixCP_5910973 : Nat.Prime 5910973 := by norm_num

private theorem prime_ninetySixCP_6682097 : Nat.Prime 6682097 := by norm_num

private theorem prime_ninetySixCP_7019203 : Nat.Prime 7019203 := by norm_num

private theorem prime_ninetySixCP_7306961 : Nat.Prime 7306961 := by norm_num

private theorem prime_ninetySixCP_7660349 : Nat.Prime 7660349 := by norm_num

private theorem prime_ninetySixCP_8016313 : Nat.Prime 8016313 := by norm_num

private theorem prime_ninetySixCP_8491487 : Nat.Prime 8491487 := by norm_num

private theorem prime_ninetySixCP_8954479 : Nat.Prime 8954479 := by norm_num

private theorem prime_ninetySixCP_9455393 : Nat.Prime 9455393 := by norm_num

private theorem prime_ninetySixCP_9920749 : Nat.Prime 9920749 := by norm_num

private theorem prime_ninetySixCP_10134233 : Nat.Prime 10134233 := by norm_num

private theorem prime_ninetySixCP_10578349 : Nat.Prime 10578349 := by norm_num

private theorem prime_ninetySixCP_12456683 : Nat.Prime 12456683 := by norm_num

private theorem prime_ninetySixCP_12559531 : Nat.Prime 12559531 := by norm_num

private theorem prime_ninetySixCP_12888803 : Nat.Prime 12888803 := by norm_num

private theorem prime_ninetySixCP_13137079 : Nat.Prime 13137079 := by norm_num

private theorem prime_ninetySixCP_13859299 : Nat.Prime 13859299 := by norm_num

private theorem prime_ninetySixCP_14097899 : Nat.Prime 14097899 := by norm_num

private theorem prime_ninetySixCP_14328493 : Nat.Prime 14328493 := by norm_num

private theorem prime_ninetySixCP_14373559 : Nat.Prime 14373559 := by norm_num

private theorem prime_ninetySixCP_14841737 : Nat.Prime 14841737 := by norm_num

private theorem prime_ninetySixCP_15274361 : Nat.Prime 15274361 := by norm_num

private theorem prime_ninetySixCP_15535111 : Nat.Prime 15535111 := by norm_num

private theorem prime_ninetySixCP_16196249 : Nat.Prime 16196249 := by norm_num

private theorem prime_ninetySixCP_16378039 : Nat.Prime 16378039 := by norm_num

private theorem prime_ninetySixCP_17895139 : Nat.Prime 17895139 := by norm_num

private theorem prime_ninetySixCP_17982271 : Nat.Prime 17982271 := by norm_num

private theorem prime_ninetySixCP_18774439 : Nat.Prime 18774439 := by norm_num

private theorem prime_ninetySixCP_21024551 : Nat.Prime 21024551 := by norm_num

private theorem prime_ninetySixCP_21945409 : Nat.Prime 21945409 := by norm_num

private theorem prime_ninetySixCP_22062361 : Nat.Prime 22062361 := by norm_num

private theorem prime_ninetySixCP_23183219 : Nat.Prime 23183219 := by norm_num

private theorem prime_ninetySixCP_25345303 : Nat.Prime 25345303 := by norm_num

private theorem prime_ninetySixCP_26106029 : Nat.Prime 26106029 := by norm_num

private theorem prime_ninetySixCP_27274349 : Nat.Prime 27274349 := by norm_num

private theorem prime_ninetySixCP_27704977 : Nat.Prime 27704977 := by norm_num

private theorem prime_ninetySixCP_31324303 : Nat.Prime 31324303 := by
  apply lucas_primality 31324303 (5 : ZMod 31324303)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (102367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (102367, 1)] : List FactorBlock).map factorBlockValue).prod) = 31324303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_102367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31324303) ^ 15662151 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31324303) ^ 10441434 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31324303) ^ 1842606 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 31324303) ^ 306 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35805727 : Nat.Prime 35805727 := by
  apply lucas_primality 35805727 (3 : ZMod 35805727)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (71, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (71, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 35805727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_71
      · exact prime_ninetySixCP_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35805727) ^ 17902863 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35805727) ^ 11935242 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35805727) ^ 3255066 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35805727) ^ 504306 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 35805727) ^ 126522 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35817917 : Nat.Prime 35817917 := by
  apply lucas_primality 35817917 (2 : ZMod 35817917)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8954479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8954479, 1)] : List FactorBlock).map factorBlockValue).prod) = 35817917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_8954479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35817917) ^ 17908958 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35817917) ^ 4 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_39469763 : Nat.Prime 39469763 := by
  apply lucas_primality 39469763 (2 : ZMod 39469763)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (64283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (64283, 1)] : List FactorBlock).map factorBlockValue).prod) = 39469763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_307
      · exact prime_ninetySixCP_64283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39469763) ^ 19734881 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 39469763) ^ 128566 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 39469763) ^ 614 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_43368791 : Nat.Prime 43368791 := by
  apply lucas_primality 43368791 (7 : ZMod 43368791)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (659, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (659, 1), (6581, 1)] : List FactorBlock).map factorBlockValue).prod) = 43368791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_659
      · exact prime_ninetySixCP_6581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 43368791) ^ 21684395 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43368791) ^ 8673758 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43368791) ^ 65810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43368791) ^ 6590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_44001809 : Nat.Prime 44001809 := by
  apply lucas_primality 44001809 (3 : ZMod 44001809)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (857, 1), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (857, 1), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) = 44001809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_857
      · exact prime_ninetySixCP_3209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44001809) ^ 22000904 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44001809) ^ 51344 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44001809) ^ 13712 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_53203519 : Nat.Prime 53203519 := by
  apply lucas_primality 53203519 (3 : ZMod 53203519)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2955751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2955751, 1)] : List FactorBlock).map factorBlockValue).prod) = 53203519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2955751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53203519) ^ 26601759 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53203519) ^ 17734506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53203519) ^ 18 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_53834551 : Nat.Prime 53834551 := by
  apply lucas_primality 53834551 (3 : ZMod 53834551)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (59, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (11, 1), (59, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) = 53834551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_79
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53834551) ^ 26917275 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 17944850 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 10766910 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 7690650 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 4894050 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 912450 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 53834551) ^ 681450 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_59380471 : Nat.Prime 59380471 := by
  apply lucas_primality 59380471 (3 : ZMod 59380471)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (659783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (659783, 1)] : List FactorBlock).map factorBlockValue).prod) = 59380471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_659783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59380471) ^ 29690235 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59380471) ^ 19793490 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59380471) ^ 11876094 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 59380471) ^ 90 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_60633869 : Nat.Prime 60633869 := by
  apply lucas_primality 60633869 (2 : ZMod 60633869)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (691, 1), (21937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (691, 1), (21937, 1)] : List FactorBlock).map factorBlockValue).prod) = 60633869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_691
      · exact prime_ninetySixCP_21937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60633869) ^ 30316934 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60633869) ^ 87748 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 60633869) ^ 2764 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_65207533 : Nat.Prime 65207533 := by
  apply lucas_primality 65207533 (5 : ZMod 65207533)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (417997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (417997, 1)] : List FactorBlock).map factorBlockValue).prod) = 65207533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_417997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65207533) ^ 32603766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 65207533) ^ 21735844 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 65207533) ^ 5015964 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 65207533) ^ 156 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_69333713 : Nat.Prime 69333713 := by
  apply lucas_primality 69333713 (5 : ZMod 69333713)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (157, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (157, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) = 69333713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_157
      · exact prime_ninetySixCP_3943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 69333713) ^ 34666856 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 69333713) ^ 9904816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 69333713) ^ 441616 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 69333713) ^ 17584 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_74698303 : Nat.Prime 74698303 := by
  apply lucas_primality 74698303 (5 : ZMod 74698303)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1778531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1778531, 1)] : List FactorBlock).map factorBlockValue).prod) = 74698303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_1778531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 74698303) ^ 37349151 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 74698303) ^ 24899434 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 74698303) ^ 10671186 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 74698303) ^ 42 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_85954783 : Nat.Prime 85954783 := by
  apply lucas_primality 85954783 (3 : ZMod 85954783)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (493993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (493993, 1)] : List FactorBlock).map factorBlockValue).prod) = 85954783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_493993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 85954783) ^ 42977391 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 85954783) ^ 28651594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 85954783) ^ 2963958 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 85954783) ^ 174 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_86380711 : Nat.Prime 86380711 := by
  apply lucas_primality 86380711 (7 : ZMod 86380711)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (221489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (221489, 1)] : List FactorBlock).map factorBlockValue).prod) = 86380711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_221489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 86380711) ^ 43190355 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 86380711) ^ 28793570 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 86380711) ^ 17276142 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 86380711) ^ 6644670 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 86380711) ^ 390 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_93908719 : Nat.Prime 93908719 := by
  apply lucas_primality 93908719 (3 : ZMod 93908719)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (197, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (197, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 93908719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_71
      · exact prime_ninetySixCP_197
      · exact prime_ninetySixCP_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93908719) ^ 46954359 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93908719) ^ 31302906 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93908719) ^ 1322658 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93908719) ^ 476694 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 93908719) ^ 251766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_113464717 : Nat.Prime 113464717 := by
  apply lucas_primality 113464717 (22 : ZMod 113464717)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9455393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9455393, 1)] : List FactorBlock).map factorBlockValue).prod) = 113464717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_9455393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (22 : ZMod 113464717) ^ 56732358 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (22 : ZMod 113464717) ^ 37821572 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (22 : ZMod 113464717) ^ 12 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_124574557 : Nat.Prime 124574557 := by
  apply lucas_primality 124574557 (5 : ZMod 124574557)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (491, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (491, 1), (21143, 1)] : List FactorBlock).map factorBlockValue).prod) = 124574557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_491
      · exact prime_ninetySixCP_21143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124574557) ^ 62287278 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 124574557) ^ 41524852 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 124574557) ^ 253716 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 124574557) ^ 5892 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_125297213 : Nat.Prime 125297213 := by
  apply lucas_primality 125297213 (2 : ZMod 125297213)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31324303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31324303, 1)] : List FactorBlock).map factorBlockValue).prod) = 125297213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_31324303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 125297213) ^ 62648606 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 125297213) ^ 4 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_129245647 : Nat.Prime 129245647 := by
  apply lucas_primality 129245647 (5 : ZMod 129245647)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2447, 1), (8803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2447, 1), (8803, 1)] : List FactorBlock).map factorBlockValue).prod) = 129245647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2447
      · exact prime_ninetySixCP_8803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129245647) ^ 64622823 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129245647) ^ 43081882 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129245647) ^ 52818 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129245647) ^ 14682 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_129908663 : Nat.Prime 129908663 := by
  apply lucas_primality 129908663 (5 : ZMod 129908663)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (19, 1), (31, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (19, 1), (31, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 129908663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 129908663) ^ 64954331 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129908663) ^ 9992974 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129908663) ^ 7641686 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129908663) ^ 6837298 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129908663) ^ 4190602 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 129908663) ^ 260338 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_130937249 : Nat.Prime 130937249 := by
  apply lucas_primality 130937249 (3 : ZMod 130937249)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (163, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (163, 1), (1931, 1)] : List FactorBlock).map factorBlockValue).prod) = 130937249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_163
      · exact prime_ninetySixCP_1931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130937249) ^ 65468624 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 130937249) ^ 10072096 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 130937249) ^ 803296 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 130937249) ^ 67808 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_140524441 : Nat.Prime 140524441 := by
  apply lucas_primality 140524441 (17 : ZMod 140524441)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (173, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (173, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 140524441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_173
      · exact prime_ninetySixCP_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 140524441) ^ 70262220 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 140524441) ^ 46841480 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 140524441) ^ 28104888 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 140524441) ^ 20074920 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 140524441) ^ 812280 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 140524441) ^ 145320 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_158160049 : Nat.Prime 158160049 := by
  apply lucas_primality 158160049 (7 : ZMod 158160049)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (73, 1), (45137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (73, 1), (45137, 1)] : List FactorBlock).map factorBlockValue).prod) = 158160049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_73
      · exact prime_ninetySixCP_45137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 158160049) ^ 79080024 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158160049) ^ 52720016 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158160049) ^ 2166576 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 158160049) ^ 3504 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_161914019 : Nat.Prime 161914019 := by
  apply lucas_primality 161914019 (2 : ZMod 161914019)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (29, 1), (23459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (29, 1), (23459, 1)] : List FactorBlock).map factorBlockValue).prod) = 161914019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_23459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161914019) ^ 80957009 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161914019) ^ 23130574 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161914019) ^ 9524354 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161914019) ^ 5583242 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 161914019) ^ 6902 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_180849649 : Nat.Prime 180849649 := by
  apply lucas_primality 180849649 (13 : ZMod 180849649)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (631, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (631, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 180849649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_631
      · exact prime_ninetySixCP_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 180849649) ^ 90424824 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 180849649) ^ 60283216 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 180849649) ^ 25835664 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 180849649) ^ 286608 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 180849649) ^ 212016 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_183848377 : Nat.Prime 183848377 := by
  apply lucas_primality 183848377 (5 : ZMod 183848377)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7660349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7660349, 1)] : List FactorBlock).map factorBlockValue).prod) = 183848377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7660349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 183848377) ^ 91924188 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 183848377) ^ 61282792 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 183848377) ^ 24 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_183886177 : Nat.Prime 183886177 := by
  apply lucas_primality 183886177 (5 : ZMod 183886177)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1915481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1915481, 1)] : List FactorBlock).map factorBlockValue).prod) = 183886177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_1915481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 183886177) ^ 91943088 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 183886177) ^ 61295392 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 183886177) ^ 96 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_187940959 : Nat.Prime 187940959 := by
  apply lucas_primality 187940959 (3 : ZMod 187940959)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (241, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (241, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 187940959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_241
      · exact prime_ninetySixCP_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 187940959) ^ 93970479 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 187940959) ^ 62646986 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 187940959) ^ 8171346 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 187940959) ^ 779838 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 187940959) ^ 33258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_196129699 : Nat.Prime 196129699 := by
  apply lucas_primality 196129699 (2 : ZMod 196129699)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (673, 1), (48571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (673, 1), (48571, 1)] : List FactorBlock).map factorBlockValue).prod) = 196129699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_673
      · exact prime_ninetySixCP_48571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 196129699) ^ 98064849 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 196129699) ^ 65376566 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 196129699) ^ 291426 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 196129699) ^ 4038 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_197281267 : Nat.Prime 197281267 := by
  apply lucas_primality 197281267 (2 : ZMod 197281267)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (361321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (361321, 1)] : List FactorBlock).map factorBlockValue).prod) = 197281267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_361321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 197281267) ^ 98640633 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197281267) ^ 65760422 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197281267) ^ 28183038 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197281267) ^ 15175482 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197281267) ^ 546 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_215515631 : Nat.Prime 215515631 := by
  apply lucas_primality 215515631 (11 : ZMod 215515631)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 1), (115249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 1), (115249, 1)] : List FactorBlock).map factorBlockValue).prod) = 215515631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_115249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 215515631) ^ 107757815 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 215515631) ^ 43103126 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 215515631) ^ 19592330 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 215515631) ^ 12677390 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 215515631) ^ 1870 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_233822753 : Nat.Prime 233822753 := by
  apply lucas_primality 233822753 (3 : ZMod 233822753)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7306961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7306961, 1)] : List FactorBlock).map factorBlockValue).prod) = 233822753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7306961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 233822753) ^ 116911376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 233822753) ^ 32 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_253687003 : Nat.Prime 253687003 := by
  apply lucas_primality 253687003 (13 : ZMod 253687003)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (322757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (322757, 1)] : List FactorBlock).map factorBlockValue).prod) = 253687003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_131
      · exact prime_ninetySixCP_322757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 253687003) ^ 126843501 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 253687003) ^ 84562334 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 253687003) ^ 1936542 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 253687003) ^ 786 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_264292151 : Nat.Prime 264292151 := by
  apply lucas_primality 264292151 (7 : ZMod 264292151)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (41, 1), (128923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (41, 1), (128923, 1)] : List FactorBlock).map factorBlockValue).prod) = 264292151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_128923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 264292151) ^ 132146075 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 264292151) ^ 52858430 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 264292151) ^ 6446150 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 264292151) ^ 2050 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_287020567 : Nat.Prime 287020567 := by
  apply lucas_primality 287020567 (5 : ZMod 287020567)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2277941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2277941, 1)] : List FactorBlock).map factorBlockValue).prod) = 287020567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_2277941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 287020567) ^ 143510283 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 287020567) ^ 95673522 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 287020567) ^ 41002938 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 287020567) ^ 126 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_315451391 : Nat.Prime 315451391 := by
  apply lucas_primality 315451391 (13 : ZMod 315451391)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (353, 1), (89363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (353, 1), (89363, 1)] : List FactorBlock).map factorBlockValue).prod) = 315451391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_353
      · exact prime_ninetySixCP_89363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 315451391) ^ 157725695 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 315451391) ^ 63090278 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 315451391) ^ 893630 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 315451391) ^ 3530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_330778867 : Nat.Prime 330778867 := by
  apply lucas_primality 330778867 (2 : ZMod 330778867)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (31, 1), (67, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (31, 1), (67, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 330778867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_67
      · exact prime_ninetySixCP_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330778867) ^ 165389433 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 110259622 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 30070806 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 17409414 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 10670286 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 4936998 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 330778867) ^ 2604558 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_358618889 : Nat.Prime 358618889 := by
  apply lucas_primality 358618889 (3 : ZMod 358618889)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (139, 1), (521, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (139, 1), (521, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 358618889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_139
      · exact prime_ninetySixCP_521
      · exact prime_ninetySixCP_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 358618889) ^ 179309444 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 358618889) ^ 2579992 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 358618889) ^ 688328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 358618889) ^ 579352 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_391245199 : Nat.Prime 391245199 := by
  apply lucas_primality 391245199 (6 : ZMod 391245199)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (65207533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (65207533, 1)] : List FactorBlock).map factorBlockValue).prod) = 391245199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_65207533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 391245199) ^ 195622599 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 391245199) ^ 130415066 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 391245199) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_399758473 : Nat.Prime 399758473 := by
  apply lucas_primality 399758473 (10 : ZMod 399758473)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5552201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5552201, 1)] : List FactorBlock).map factorBlockValue).prod) = 399758473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5552201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 399758473) ^ 199879236 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 399758473) ^ 133252824 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 399758473) ^ 72 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_400670147 : Nat.Prime 400670147 := by
  apply lucas_primality 400670147 (2 : ZMod 400670147)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (2535887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (2535887, 1)] : List FactorBlock).map factorBlockValue).prod) = 400670147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_79
      · exact prime_ninetySixCP_2535887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 400670147) ^ 200335073 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 400670147) ^ 5071774 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 400670147) ^ 158 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_423637937 : Nat.Prime 423637937 := by
  apply lucas_primality 423637937 (3 : ZMod 423637937)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (59, 1), (448769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (59, 1), (448769, 1)] : List FactorBlock).map factorBlockValue).prod) = 423637937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_448769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 423637937) ^ 211818968 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 423637937) ^ 7180304 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 423637937) ^ 944 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_448866863 : Nat.Prime 448866863 := by
  apply lucas_primality 448866863 (5 : ZMod 448866863)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1614629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1614629, 1)] : List FactorBlock).map factorBlockValue).prod) = 448866863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_139
      · exact prime_ninetySixCP_1614629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 448866863) ^ 224433431 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 448866863) ^ 3229258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 448866863) ^ 278 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_451132769 : Nat.Prime 451132769 := by
  apply lucas_primality 451132769 (3 : ZMod 451132769)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (14097899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (14097899, 1)] : List FactorBlock).map factorBlockValue).prod) = 451132769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_14097899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 451132769) ^ 225566384 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451132769) ^ 32 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_451181323 : Nat.Prime 451181323 := by
  apply lucas_primality 451181323 (3 : ZMod 451181323)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (307, 1), (81647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (307, 1), (81647, 1)] : List FactorBlock).map factorBlockValue).prod) = 451181323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_307
      · exact prime_ninetySixCP_81647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 451181323) ^ 225590661 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451181323) ^ 150393774 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451181323) ^ 1469646 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 451181323) ^ 5526 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_466560821 : Nat.Prime 466560821 := by
  apply lucas_primality 466560821 (2 : ZMod 466560821)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (2120731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (2120731, 1)] : List FactorBlock).map factorBlockValue).prod) = 466560821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_2120731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 466560821) ^ 233280410 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 466560821) ^ 93312164 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 466560821) ^ 42414620 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 466560821) ^ 220 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_519309221 : Nat.Prime 519309221 := by
  apply lucas_primality 519309221 (2 : ZMod 519309221)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1249, 1), (20789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1249, 1), (20789, 1)] : List FactorBlock).map factorBlockValue).prod) = 519309221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_1249
      · exact prime_ninetySixCP_20789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 519309221) ^ 259654610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 519309221) ^ 103861844 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 519309221) ^ 415780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 519309221) ^ 24980 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_558112297 : Nat.Prime 558112297 := by
  apply lucas_primality 558112297 (5 : ZMod 558112297)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (144439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (144439, 1)] : List FactorBlock).map factorBlockValue).prod) = 558112297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_144439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 558112297) ^ 279056148 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 558112297) ^ 186037432 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 558112297) ^ 79730328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 558112297) ^ 24265752 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 558112297) ^ 3864 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_579285533 : Nat.Prime 579285533 := by
  apply lucas_primality 579285533 (2 : ZMod 579285533)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (233, 1), (88793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (233, 1), (88793, 1)] : List FactorBlock).map factorBlockValue).prod) = 579285533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_233
      · exact prime_ninetySixCP_88793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 579285533) ^ 289642766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 579285533) ^ 82755076 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 579285533) ^ 2486204 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 579285533) ^ 6524 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_625127449 : Nat.Prime 625127449 := by
  apply lucas_primality 625127449 (13 : ZMod 625127449)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (47, 1), (83, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (47, 1), (83, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 625127449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_47
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 625127449) ^ 312563724 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 625127449) ^ 208375816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 625127449) ^ 56829768 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 625127449) ^ 13300584 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 625127449) ^ 7531656 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 625127449) ^ 1029864 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_628860857 : Nat.Prime 628860857 := by
  apply lucas_primality 628860857 (3 : ZMod 628860857)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (76541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (76541, 1)] : List FactorBlock).map factorBlockValue).prod) = 628860857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_79
      · exact prime_ninetySixCP_76541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 628860857) ^ 314430428 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 628860857) ^ 48373912 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 628860857) ^ 7960264 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 628860857) ^ 8216 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_657284633 : Nat.Prime 657284633 := by
  apply lucas_primality 657284633 (3 : ZMod 657284633)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (1187, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (1187, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 657284633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_1187
      · exact prime_ninetySixCP_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 657284633) ^ 328642316 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 657284633) ^ 34593928 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 657284633) ^ 553736 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 657284633) ^ 180424 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_721405981 : Nat.Prime 721405981 := by
  apply lucas_primality 721405981 (2 : ZMod 721405981)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (59, 1), (22643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (59, 1), (22643, 1)] : List FactorBlock).map factorBlockValue).prod) = 721405981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_22643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 721405981) ^ 360702990 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 721405981) ^ 240468660 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 721405981) ^ 144281196 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 721405981) ^ 12227220 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 721405981) ^ 31860 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_896340773 : Nat.Prime 896340773 := by
  apply lucas_primality 896340773 (2 : ZMod 896340773)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1321, 1), (169633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1321, 1), (169633, 1)] : List FactorBlock).map factorBlockValue).prod) = 896340773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_1321
      · exact prime_ninetySixCP_169633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 896340773) ^ 448170386 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 896340773) ^ 678532 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 896340773) ^ 5284 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_965335247 : Nat.Prime 965335247 := by
  apply lucas_primality 965335247 (5 : ZMod 965335247)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14411, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14411, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) = 965335247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_14411
      · exact prime_ninetySixCP_33493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 965335247) ^ 482667623 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 965335247) ^ 66986 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 965335247) ^ 28822 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_968329457 : Nat.Prime 968329457 := by
  apply lucas_primality 968329457 (3 : ZMod 968329457)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (565613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (565613, 1)] : List FactorBlock).map factorBlockValue).prod) = 968329457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_565613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 968329457) ^ 484164728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 968329457) ^ 9049808 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 968329457) ^ 1712 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1154685793 : Nat.Prime 1154685793 := by
  apply lucas_primality 1154685793 (5 : ZMod 1154685793)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (107, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (107, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1154685793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_8647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1154685793) ^ 577342896 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1154685793) ^ 384895264 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1154685793) ^ 88821984 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1154685793) ^ 10791456 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1154685793) ^ 133536 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1194016547 : Nat.Prime 1194016547 := by
  apply lucas_primality 1194016547 (2 : ZMod 1194016547)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (5910973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (5910973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1194016547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_5910973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1194016547) ^ 597008273 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1194016547) ^ 11821946 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1194016547) ^ 202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1252659731 : Nat.Prime 1252659731 := by
  apply lucas_primality 1252659731 (2 : ZMod 1252659731)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17895139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17895139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252659731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_17895139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1252659731) ^ 626329865 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252659731) ^ 250531946 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252659731) ^ 178951390 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252659731) ^ 70 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1362297619 : Nat.Prime 1362297619 := by
  apply lucas_primality 1362297619 (2 : ZMod 1362297619)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (17, 1), (36793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (17, 1), (36793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362297619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_36793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1362297619) ^ 681148809 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362297619) ^ 454099206 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362297619) ^ 123845238 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362297619) ^ 80135154 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362297619) ^ 37026 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1402936519 : Nat.Prime 1402936519 := by
  apply lucas_primality 1402936519 (15 : ZMod 1402936519)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (233822753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (233822753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1402936519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_233822753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 1402936519) ^ 701468259 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 1402936519) ^ 467645506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 1402936519) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1599033893 : Nat.Prime 1599033893 := by
  apply lucas_primality 1599033893 (2 : ZMod 1599033893)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (399758473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (399758473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1599033893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_399758473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1599033893) ^ 799516946 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1599033893) ^ 4 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1636584511 : Nat.Prime 1636584511 := by
  apply lucas_primality 1636584511 (3 : ZMod 1636584511)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (89, 1), (103, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (89, 1), (103, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1636584511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_89
      · exact prime_ninetySixCP_103
      · exact prime_ninetySixCP_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1636584511) ^ 818292255 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 545528170 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 327316902 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 148780410 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 18388590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 15889170 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1636584511) ^ 3025110 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1785805603 : Nat.Prime 1785805603 := by
  apply lucas_primality 1785805603 (2 : ZMod 1785805603)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1153, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1153, 1), (36877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1785805603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_1153
      · exact prime_ninetySixCP_36877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1785805603) ^ 892902801 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785805603) ^ 595268534 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785805603) ^ 255115086 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785805603) ^ 1548834 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785805603) ^ 48426 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1972242067 : Nat.Prime 1972242067 := by
  apply lucas_primality 1972242067 (19 : ZMod 1972242067)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (271, 1), (63839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (271, 1), (63839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1972242067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_271
      · exact prime_ninetySixCP_63839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1972242067) ^ 986121033 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1972242067) ^ 657414022 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1972242067) ^ 103802214 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1972242067) ^ 7277646 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 1972242067) ^ 30894 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2108506783 : Nat.Prime 2108506783 := by
  apply lucas_primality 2108506783 (3 : ZMod 2108506783)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (283, 1), (953, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (283, 1), (953, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 2108506783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_283
      · exact prime_ninetySixCP_953
      · exact prime_ninetySixCP_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2108506783) ^ 1054253391 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2108506783) ^ 702835594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2108506783) ^ 7450554 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2108506783) ^ 2212494 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2108506783) ^ 1618194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2310323513 : Nat.Prime 2310323513 := by
  apply lucas_primality 2310323513 (3 : ZMod 2310323513)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (29, 1), (37, 1), (38449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (29, 1), (37, 1), (38449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2310323513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_38449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2310323513) ^ 1155161756 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2310323513) ^ 330046216 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2310323513) ^ 79666328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2310323513) ^ 62441176 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2310323513) ^ 60088 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2456705851 : Nat.Prime 2456705851 := by
  apply lucas_primality 2456705851 (3 : ZMod 2456705851)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (16378039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (16378039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2456705851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_16378039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2456705851) ^ 1228352925 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2456705851) ^ 818901950 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2456705851) ^ 491341170 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2456705851) ^ 150 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2500261333 : Nat.Prime 2500261333 := by
  apply lucas_primality 2500261333 (2 : ZMod 2500261333)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (29, 1), (422627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (29, 1), (422627, 1)] : List FactorBlock).map factorBlockValue).prod) = 2500261333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_422627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2500261333) ^ 1250130666 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2500261333) ^ 833420444 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2500261333) ^ 147074196 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2500261333) ^ 86215908 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2500261333) ^ 5916 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2500509797 : Nat.Prime 2500509797 := by
  apply lucas_primality 2500509797 (2 : ZMod 2500509797)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (625127449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (625127449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2500509797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_625127449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2500509797) ^ 1250254898 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2500509797) ^ 4 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2534530301 : Nat.Prime 2534530301 := by
  apply lucas_primality 2534530301 (2 : ZMod 2534530301)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (25345303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (25345303, 1)] : List FactorBlock).map factorBlockValue).prod) = 2534530301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_25345303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2534530301) ^ 1267265150 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2534530301) ^ 506906060 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2534530301) ^ 100 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2767128761 : Nat.Prime 2767128761 := by
  apply lucas_primality 2767128761 (3 : ZMod 2767128761)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (17, 2), (47, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (17, 2), (47, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2767128761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_47
      · exact prime_ninetySixCP_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2767128761) ^ 1383564380 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767128761) ^ 553425752 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767128761) ^ 251557160 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767128761) ^ 162772280 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767128761) ^ 58875080 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2767128761) ^ 5976520 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3382937263 : Nat.Prime 3382937263 := by
  apply lucas_primality 3382937263 (3 : ZMod 3382937263)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (187940959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (187940959, 1)] : List FactorBlock).map factorBlockValue).prod) = 3382937263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_187940959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3382937263) ^ 1691468631 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3382937263) ^ 1127645754 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3382937263) ^ 18 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3610387367 : Nat.Prime 3610387367 := by
  apply lucas_primality 3610387367 (5 : ZMod 3610387367)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (1571, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (1571, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) = 3610387367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_1571
      · exact prime_ninetySixCP_10739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3610387367) ^ 1805193683 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3610387367) ^ 33741938 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3610387367) ^ 2298146 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3610387367) ^ 336194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_4705518583 : Nat.Prime 4705518583 := by
  apply lucas_primality 4705518583 (3 : ZMod 4705518583)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (31, 1), (34703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (31, 1), (34703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4705518583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_34703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4705518583) ^ 2352759291 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4705518583) ^ 1568506194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4705518583) ^ 151790922 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4705518583) ^ 135594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5156978581 : Nat.Prime 5156978581 := by
  apply lucas_primality 5156978581 (2 : ZMod 5156978581)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (95819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (95819, 1)] : List FactorBlock).map factorBlockValue).prod) = 5156978581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_95819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5156978581) ^ 2578489290 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5156978581) ^ 1718992860 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5156978581) ^ 1031395716 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5156978581) ^ 396690660 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5156978581) ^ 224216460 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5156978581) ^ 53820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5534257523 : Nat.Prime 5534257523 := by
  apply lucas_primality 5534257523 (2 : ZMod 5534257523)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2767128761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2767128761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5534257523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_2767128761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5534257523) ^ 2767128761 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5534257523) ^ 2 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5585811137 : Nat.Prime 5585811137 := by
  apply lucas_primality 5585811137 (5 : ZMod 5585811137)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (31, 1), (41, 1), (68669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (31, 1), (41, 1), (68669, 1)] : List FactorBlock).map factorBlockValue).prod) = 5585811137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_68669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5585811137) ^ 2792905568 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5585811137) ^ 180187456 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5585811137) ^ 136239296 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5585811137) ^ 81344 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5678125039 : Nat.Prime 5678125039 := by
  apply lucas_primality 5678125039 (6 : ZMod 5678125039)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (315451391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (315451391, 1)] : List FactorBlock).map factorBlockValue).prod) = 5678125039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_315451391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5678125039) ^ 2839062519 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 5678125039) ^ 1892708346 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 5678125039) ^ 18 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_8351108281 : Nat.Prime 8351108281 := by
  apply lucas_primality 8351108281 (7 : ZMod 8351108281)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (191, 1), (121453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (191, 1), (121453, 1)] : List FactorBlock).map factorBlockValue).prod) = 8351108281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_191
      · exact prime_ninetySixCP_121453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8351108281) ^ 4175554140 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351108281) ^ 2783702760 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351108281) ^ 1670221656 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351108281) ^ 43723080 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351108281) ^ 68760 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_8824066327 : Nat.Prime 8824066327 := by
  apply lucas_primality 8824066327 (6 : ZMod 8824066327)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1301, 1), (376807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1301, 1), (376807, 1)] : List FactorBlock).map factorBlockValue).prod) = 8824066327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_1301
      · exact prime_ninetySixCP_376807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 8824066327) ^ 4412033163 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8824066327) ^ 2941355442 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8824066327) ^ 6782526 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8824066327) ^ 23418 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_9143445161 : Nat.Prime 9143445161 := by
  apply lucas_primality 9143445161 (3 : ZMod 9143445161)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (2263229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (2263229, 1)] : List FactorBlock).map factorBlockValue).prod) = 9143445161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_2263229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9143445161) ^ 4571722580 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9143445161) ^ 1828689032 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9143445161) ^ 90529160 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9143445161) ^ 4040 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_9514646611 : Nat.Prime 9514646611 := by
  apply lucas_primality 9514646611 (2 : ZMod 9514646611)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (4219, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (4219, 1), (10739, 1)] : List FactorBlock).map factorBlockValue).prod) = 9514646611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_4219
      · exact prime_ninetySixCP_10739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9514646611) ^ 4757323305 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9514646611) ^ 3171548870 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9514646611) ^ 1902929322 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9514646611) ^ 1359235230 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9514646611) ^ 2255190 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9514646611) ^ 885990 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_10228564691 : Nat.Prime 10228564691 := by
  apply lucas_primality 10228564691 (6 : ZMod 10228564691)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (53834551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (53834551, 1)] : List FactorBlock).map factorBlockValue).prod) = 10228564691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_53834551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10228564691) ^ 5114282345 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10228564691) ^ 2045712938 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10228564691) ^ 538345510 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 10228564691) ^ 190 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_10799683561 : Nat.Prime 10799683561 := by
  apply lucas_primality 10799683561 (19 : ZMod 10799683561)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (101, 1), (181, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (101, 1), (181, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 10799683561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_181
      · exact prime_ninetySixCP_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 10799683561) ^ 5399841780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 10799683561) ^ 3599894520 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 10799683561) ^ 2159936712 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 10799683561) ^ 106927560 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 10799683561) ^ 59666760 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 10799683561) ^ 19743480 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_11590531741 : Nat.Prime 11590531741 := by
  apply lucas_primality 11590531741 (2 : ZMod 11590531741)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (101, 1), (637543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (101, 1), (637543, 1)] : List FactorBlock).map factorBlockValue).prod) = 11590531741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_637543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11590531741) ^ 5795265870 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11590531741) ^ 3863510580 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11590531741) ^ 2318106348 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11590531741) ^ 114757740 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11590531741) ^ 18180 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_11852904137 : Nat.Prime 11852904137 := by
  apply lucas_primality 11852904137 (3 : ZMod 11852904137)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (15274361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (15274361, 1)] : List FactorBlock).map factorBlockValue).prod) = 11852904137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_97
      · exact prime_ninetySixCP_15274361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11852904137) ^ 5926452068 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 11852904137) ^ 122194888 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 11852904137) ^ 776 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_12160417393 : Nat.Prime 12160417393 := by
  apply lucas_primality 12160417393 (7 : ZMod 12160417393)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (193, 1), (23029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (193, 1), (23029, 1)] : List FactorBlock).map factorBlockValue).prod) = 12160417393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_193
      · exact prime_ninetySixCP_23029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12160417393) ^ 6080208696 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12160417393) ^ 4053472464 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12160417393) ^ 640021968 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12160417393) ^ 63007344 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12160417393) ^ 528048 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_13218183443 : Nat.Prime 13218183443 := by
  apply lucas_primality 13218183443 (2 : ZMod 13218183443)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (60633869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (60633869, 1)] : List FactorBlock).map factorBlockValue).prod) = 13218183443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_109
      · exact prime_ninetySixCP_60633869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13218183443) ^ 6609091721 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13218183443) ^ 121267738 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13218183443) ^ 218 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_14029365191 : Nat.Prime 14029365191 := by
  apply lucas_primality 14029365191 (7 : ZMod 14029365191)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1402936519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1402936519, 1)] : List FactorBlock).map factorBlockValue).prod) = 14029365191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_1402936519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 14029365191) ^ 7014682595 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 14029365191) ^ 2805873038 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 14029365191) ^ 10 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_14942647117 : Nat.Prime 14942647117 := by
  apply lucas_primality 14942647117 (2 : ZMod 14942647117)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2857, 1), (145283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2857, 1), (145283, 1)] : List FactorBlock).map factorBlockValue).prod) = 14942647117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2857
      · exact prime_ninetySixCP_145283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14942647117) ^ 7471323558 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14942647117) ^ 4980882372 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14942647117) ^ 5230188 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14942647117) ^ 102852 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_16386113363 : Nat.Prime 16386113363 := by
  apply lucas_primality 16386113363 (2 : ZMod 16386113363)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (264292151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (264292151, 1)] : List FactorBlock).map factorBlockValue).prod) = 16386113363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_264292151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16386113363) ^ 8193056681 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 16386113363) ^ 528584302 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 16386113363) ^ 62 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_16577300461 : Nat.Prime 16577300461 := by
  apply lucas_primality 16577300461 (10 : ZMod 16577300461)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (39469763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (39469763, 1)] : List FactorBlock).map factorBlockValue).prod) = 16577300461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_39469763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16577300461) ^ 8288650230 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 16577300461) ^ 5525766820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 16577300461) ^ 3315460092 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 16577300461) ^ 2368185780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 16577300461) ^ 420 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_16585096513 : Nat.Prime 16585096513 := by
  apply lucas_primality 16585096513 (5 : ZMod 16585096513)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (86380711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (86380711, 1)] : List FactorBlock).map factorBlockValue).prod) = 16585096513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_86380711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16585096513) ^ 8292548256 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16585096513) ^ 5528365504 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16585096513) ^ 192 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_17717488933 : Nat.Prime 17717488933 := by
  apply lucas_primality 17717488933 (2 : ZMod 17717488933)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (53, 1), (194809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (53, 1), (194809, 1)] : List FactorBlock).map factorBlockValue).prod) = 17717488933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_194809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17717488933) ^ 8858744466 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717488933) ^ 5905829644 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717488933) ^ 1610680812 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717488933) ^ 1362883764 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717488933) ^ 334292244 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17717488933) ^ 90948 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_20490684131 : Nat.Prime 20490684131 := by
  apply lucas_primality 20490684131 (2 : ZMod 20490684131)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (149, 1), (229, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (149, 1), (229, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 20490684131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_149
      · exact prime_ninetySixCP_229
      · exact prime_ninetySixCP_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20490684131) ^ 10245342065 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 4098136826 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 2927240590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 890899310 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 137521370 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 89478970 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20490684131) ^ 54934810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_21312013699 : Nat.Prime 21312013699 := by
  apply lucas_primality 21312013699 (3 : ZMod 21312013699)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (229, 1), (97553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (229, 1), (97553, 1)] : List FactorBlock).map factorBlockValue).prod) = 21312013699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_229
      · exact prime_ninetySixCP_97553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21312013699) ^ 10656006849 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21312013699) ^ 7104004566 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21312013699) ^ 402113466 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21312013699) ^ 93065562 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 21312013699) ^ 218466 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_23985900317 : Nat.Prime 23985900317 := by
  apply lucas_primality 23985900317 (2 : ZMod 23985900317)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3083, 1), (277859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3083, 1), (277859, 1)] : List FactorBlock).map factorBlockValue).prod) = 23985900317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_3083
      · exact prime_ninetySixCP_277859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23985900317) ^ 11992950158 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23985900317) ^ 3426557188 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23985900317) ^ 7780052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23985900317) ^ 86324 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_29480470213 : Nat.Prime 29480470213 := by
  apply lucas_primality 29480470213 (2 : ZMod 29480470213)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2456705851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2456705851, 1)] : List FactorBlock).map factorBlockValue).prod) = 29480470213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2456705851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29480470213) ^ 14740235106 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29480470213) ^ 9826823404 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29480470213) ^ 12 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_30117622753 : Nat.Prime 30117622753 := by
  apply lucas_primality 30117622753 (5 : ZMod 30117622753)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (557, 1), (26821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (557, 1), (26821, 1)] : List FactorBlock).map factorBlockValue).prod) = 30117622753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_557
      · exact prime_ninetySixCP_26821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30117622753) ^ 15058811376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30117622753) ^ 10039207584 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30117622753) ^ 4302517536 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30117622753) ^ 54071136 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 30117622753) ^ 1122912 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_33829372631 : Nat.Prime 33829372631 := by
  apply lucas_primality 33829372631 (13 : ZMod 33829372631)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3382937263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3382937263, 1)] : List FactorBlock).map factorBlockValue).prod) = 33829372631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_3382937263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 33829372631) ^ 16914686315 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 33829372631) ^ 6765874526 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 33829372631) ^ 10 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_37817585753 : Nat.Prime 37817585753 := by
  apply lucas_primality 37817585753 (3 : ZMod 37817585753)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109, 1), (43368791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109, 1), (43368791, 1)] : List FactorBlock).map factorBlockValue).prod) = 37817585753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_109
      · exact prime_ninetySixCP_43368791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37817585753) ^ 18908792876 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37817585753) ^ 346950328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 37817585753) ^ 872 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_41942184737 : Nat.Prime 41942184737 := by
  apply lucas_primality 41942184737 (3 : ZMod 41942184737)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (463, 1), (2830871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (463, 1), (2830871, 1)] : List FactorBlock).map factorBlockValue).prod) = 41942184737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_463
      · exact prime_ninetySixCP_2830871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41942184737) ^ 20971092368 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41942184737) ^ 90587872 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 41942184737) ^ 14816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_44967188839 : Nat.Prime 44967188839 := by
  apply lucas_primality 44967188839 (3 : ZMod 44967188839)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (79, 1), (663409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (79, 1), (663409, 1)] : List FactorBlock).map factorBlockValue).prod) = 44967188839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_79
      · exact prime_ninetySixCP_663409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44967188839) ^ 22483594419 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44967188839) ^ 14989062946 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44967188839) ^ 4087926258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44967188839) ^ 3459014526 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44967188839) ^ 569204922 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 44967188839) ^ 67782 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_46409590613 : Nat.Prime 46409590613 := by
  apply lucas_primality 46409590613 (2 : ZMod 46409590613)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (2441, 1), (61729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (2441, 1), (61729, 1)] : List FactorBlock).map factorBlockValue).prod) = 46409590613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_2441
      · exact prime_ninetySixCP_61729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46409590613) ^ 23204795306 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46409590613) ^ 6629941516 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46409590613) ^ 4219053692 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46409590613) ^ 19012532 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46409590613) ^ 751828 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_50538607897 : Nat.Prime 50538607897 := by
  apply lucas_primality 50538607897 (5 : ZMod 50538607897)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (193, 1), (277, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (193, 1), (277, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 50538607897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_193
      · exact prime_ninetySixCP_277
      · exact prime_ninetySixCP_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50538607897) ^ 25269303948 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 16846202632 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 7219801128 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 2972859288 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 261858072 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 182449848 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 50538607897) ^ 152684616 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_50980672697 : Nat.Prime 50980672697 := by
  apply lucas_primality 50980672697 (3 : ZMod 50980672697)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (12973, 1), (491219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (12973, 1), (491219, 1)] : List FactorBlock).map factorBlockValue).prod) = 50980672697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_12973
      · exact prime_ninetySixCP_491219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50980672697) ^ 25490336348 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50980672697) ^ 3929752 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50980672697) ^ 103784 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_51228802243 : Nat.Prime 51228802243 := by
  apply lucas_primality 51228802243 (2 : ZMod 51228802243)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (22062361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (22062361, 1)] : List FactorBlock).map factorBlockValue).prod) = 51228802243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_43
      · exact prime_ninetySixCP_22062361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51228802243) ^ 25614401121 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51228802243) ^ 17076267414 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51228802243) ^ 1191367494 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 51228802243) ^ 2322 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_52944397963 : Nat.Prime 52944397963 := by
  apply lucas_primality 52944397963 (3 : ZMod 52944397963)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8824066327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8824066327, 1)] : List FactorBlock).map factorBlockValue).prod) = 52944397963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_8824066327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52944397963) ^ 26472198981 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52944397963) ^ 17648132654 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52944397963) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_59158491019 : Nat.Prime 59158491019 := by
  apply lucas_primality 59158491019 (10 : ZMod 59158491019)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (896340773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (896340773, 1)] : List FactorBlock).map factorBlockValue).prod) = 59158491019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_896340773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 59158491019) ^ 29579245509 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 59158491019) ^ 19719497006 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 59158491019) ^ 5378044638 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 59158491019) ^ 66 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_69543190447 : Nat.Prime 69543190447 := by
  apply lucas_primality 69543190447 (3 : ZMod 69543190447)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11590531741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11590531741, 1)] : List FactorBlock).map factorBlockValue).prod) = 69543190447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11590531741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 69543190447) ^ 34771595223 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69543190447) ^ 23181063482 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69543190447) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_69708040697 : Nat.Prime 69708040697 := by
  apply lucas_primality 69708040697 (3 : ZMod 69708040697)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (83, 1), (1597, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (83, 1), (1597, 1), (9391, 1)] : List FactorBlock).map factorBlockValue).prod) = 69708040697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_1597
      · exact prime_ninetySixCP_9391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69708040697) ^ 34854020348 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69708040697) ^ 9958291528 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69708040697) ^ 839855912 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69708040697) ^ 43649368 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 69708040697) ^ 7422856 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_78786380221 : Nat.Prime 78786380221 := by
  apply lucas_primality 78786380221 (2 : ZMod 78786380221)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (449, 1), (2924513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (449, 1), (2924513, 1)] : List FactorBlock).map factorBlockValue).prod) = 78786380221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_449
      · exact prime_ninetySixCP_2924513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78786380221) ^ 39393190110 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 78786380221) ^ 26262126740 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 78786380221) ^ 15757276044 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 78786380221) ^ 175470780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 78786380221) ^ 26940 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_92819181227 : Nat.Prime 92819181227 := by
  apply lucas_primality 92819181227 (2 : ZMod 92819181227)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46409590613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46409590613, 1)] : List FactorBlock).map factorBlockValue).prod) = 92819181227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_46409590613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 92819181227) ^ 46409590613 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 92819181227) ^ 2 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_114921956417 : Nat.Prime 114921956417 := by
  apply lucas_primality 114921956417 (3 : ZMod 114921956417)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (181, 1), (9920749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (181, 1), (9920749, 1)] : List FactorBlock).map factorBlockValue).prod) = 114921956417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_181
      · exact prime_ninetySixCP_9920749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 114921956417) ^ 57460978208 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 114921956417) ^ 634927936 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 114921956417) ^ 11584 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_139137708727 : Nat.Prime 139137708727 := by
  apply lucas_primality 139137708727 (29 : ZMod 139137708727)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (4871, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (4871, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) = 139137708727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_4871
      · exact prime_ninetySixCP_14831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 139137708727) ^ 69568854363 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (29 : ZMod 139137708727) ^ 46379236242 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (29 : ZMod 139137708727) ^ 1300352418 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (29 : ZMod 139137708727) ^ 28564506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (29 : ZMod 139137708727) ^ 9381546 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_176614893061 : Nat.Prime 176614893061 := by
  apply lucas_primality 176614893061 (2 : ZMod 176614893061)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 1), (607, 1), (72379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 1), (607, 1), (72379, 1)] : List FactorBlock).map factorBlockValue).prod) = 176614893061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_67
      · exact prime_ninetySixCP_607
      · exact prime_ninetySixCP_72379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 176614893061) ^ 88307446530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176614893061) ^ 58871631020 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176614893061) ^ 35322978612 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176614893061) ^ 2636043180 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176614893061) ^ 290963580 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 176614893061) ^ 2440140 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_187846779641 : Nat.Prime 187846779641 := by
  apply lucas_primality 187846779641 (6 : ZMod 187846779641)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (29, 1), (12456683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (29, 1), (12456683, 1)] : List FactorBlock).map factorBlockValue).prod) = 187846779641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_12456683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 187846779641) ^ 93923389820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 187846779641) ^ 37569355928 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 187846779641) ^ 14449752280 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 187846779641) ^ 6477475160 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 187846779641) ^ 15080 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_213019620067 : Nat.Prime 213019620067 := by
  apply lucas_primality 213019620067 (5 : ZMod 213019620067)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (358618889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (358618889, 1)] : List FactorBlock).map factorBlockValue).prod) = 213019620067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_358618889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213019620067) ^ 106509810033 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 213019620067) ^ 71006540022 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 213019620067) ^ 19365420006 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 213019620067) ^ 594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_237541372813 : Nat.Prime 237541372813 := by
  apply lucas_primality 237541372813 (2 : ZMod 237541372813)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (313, 1), (331, 1), (63689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (313, 1), (331, 1), (63689, 1)] : List FactorBlock).map factorBlockValue).prod) = 237541372813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_313
      · exact prime_ninetySixCP_331
      · exact prime_ninetySixCP_63689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237541372813) ^ 118770686406 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237541372813) ^ 79180457604 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237541372813) ^ 758918124 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237541372813) ^ 717647652 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237541372813) ^ 3729708 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_294527949497 : Nat.Prime 294527949497 := by
  apply lucas_primality 294527949497 (3 : ZMod 294527949497)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (59, 1), (83, 1), (683461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (59, 1), (83, 1), (683461, 1)] : List FactorBlock).map factorBlockValue).prod) = 294527949497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_683461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 294527949497) ^ 147263974748 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 294527949497) ^ 26775268136 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 294527949497) ^ 4991999144 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 294527949497) ^ 3548529512 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 294527949497) ^ 430936 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_303725278319 : Nat.Prime 303725278319 := by
  apply lucas_primality 303725278319 (7 : ZMod 303725278319)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1972242067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1972242067, 1)] : List FactorBlock).map factorBlockValue).prod) = 303725278319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_1972242067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 303725278319) ^ 151862639159 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 303725278319) ^ 43389325474 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 303725278319) ^ 27611388938 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 303725278319) ^ 154 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_368663535043 : Nat.Prime 368663535043 := by
  apply lucas_primality 368663535043 (2 : ZMod 368663535043)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5585811137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5585811137, 1)] : List FactorBlock).map factorBlockValue).prod) = 368663535043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_5585811137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 368663535043) ^ 184331767521 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 368663535043) ^ 122887845014 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 368663535043) ^ 33514866822 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 368663535043) ^ 66 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_426964954657 : Nat.Prime 426964954657 := by
  apply lucas_primality 426964954657 (7 : ZMod 426964954657)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (241, 1), (277, 1), (3919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (241, 1), (277, 1), (3919, 1)] : List FactorBlock).map factorBlockValue).prod) = 426964954657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_241
      · exact prime_ninetySixCP_277
      · exact prime_ninetySixCP_3919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 426964954657) ^ 213482477328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 426964954657) ^ 142321651552 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 426964954657) ^ 25115585568 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 426964954657) ^ 1771638816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 426964954657) ^ 1541389728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 426964954657) ^ 108947424 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_428591578159 : Nat.Prime 428591578159 := by
  apply lucas_primality 428591578159 (15 : ZMod 428591578159)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (1321, 1), (316223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (1321, 1), (316223, 1)] : List FactorBlock).map factorBlockValue).prod) = 428591578159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_1321
      · exact prime_ninetySixCP_316223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 428591578159) ^ 214295789079 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 428591578159) ^ 142863859386 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 428591578159) ^ 22557451482 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 428591578159) ^ 324444798 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (15 : ZMod 428591578159) ^ 1355346 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_438885121999 : Nat.Prime 438885121999 := by
  apply lucas_primality 438885121999 (3 : ZMod 438885121999)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (37, 1), (85954783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (37, 1), (85954783, 1)] : List FactorBlock).map factorBlockValue).prod) = 438885121999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_85954783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 438885121999) ^ 219442560999 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 438885121999) ^ 146295040666 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 438885121999) ^ 19081961826 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 438885121999) ^ 11861760054 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 438885121999) ^ 5106 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_521984302129 : Nat.Prime 521984302129 := by
  apply lucas_primality 521984302129 (14 : ZMod 521984302129)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (719, 1), (5041573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (719, 1), (5041573, 1)] : List FactorBlock).map factorBlockValue).prod) = 521984302129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_719
      · exact prime_ninetySixCP_5041573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 521984302129) ^ 260992151064 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 521984302129) ^ 173994767376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 521984302129) ^ 725986512 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 521984302129) ^ 103536 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_575562782393 : Nat.Prime 575562782393 := by
  apply lucas_primality 575562782393 (3 : ZMod 575562782393)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (5534257523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (5534257523, 1)] : List FactorBlock).map factorBlockValue).prod) = 575562782393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_5534257523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 575562782393) ^ 287781391196 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 575562782393) ^ 44274060184 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 575562782393) ^ 104 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_598974037489 : Nat.Prime 598974037489 := by
  apply lucas_primality 598974037489 (38 : ZMod 598974037489)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (180849649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (180849649, 1)] : List FactorBlock).map factorBlockValue).prod) = 598974037489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_180849649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (38 : ZMod 598974037489) ^ 299487018744 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (38 : ZMod 598974037489) ^ 199658012496 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (38 : ZMod 598974037489) ^ 26042349456 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (38 : ZMod 598974037489) ^ 3312 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_607450556639 : Nat.Prime 607450556639 := by
  apply lucas_primality 607450556639 (11 : ZMod 607450556639)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (303725278319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (303725278319, 1)] : List FactorBlock).map factorBlockValue).prod) = 607450556639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_303725278319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 607450556639) ^ 303725278319 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 607450556639) ^ 2 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_623148868409 : Nat.Prime 623148868409 := by
  apply lucas_primality 623148868409 (3 : ZMod 623148868409)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 3), (41, 1), (277, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 3), (41, 1), (277, 1), (5153, 1)] : List FactorBlock).map factorBlockValue).prod) = 623148868409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_277
      · exact prime_ninetySixCP_5153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 623148868409) ^ 311574434204 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 623148868409) ^ 56649897128 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 623148868409) ^ 15198752888 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 623148868409) ^ 2249634904 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 623148868409) ^ 120929336 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_635332775557 : Nat.Prime 635332775557 := by
  apply lucas_primality 635332775557 (23 : ZMod 635332775557)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (52944397963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (52944397963, 1)] : List FactorBlock).map factorBlockValue).prod) = 635332775557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_52944397963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 635332775557) ^ 317666387778 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (23 : ZMod 635332775557) ^ 211777591852 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (23 : ZMod 635332775557) ^ 12 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_670407215531 : Nat.Prime 670407215531 := by
  apply lucas_primality 670407215531 (2 : ZMod 670407215531)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (5156978581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (5156978581, 1)] : List FactorBlock).map factorBlockValue).prod) = 670407215531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_5156978581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 670407215531) ^ 335203607765 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 670407215531) ^ 134081443106 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 670407215531) ^ 51569785810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 670407215531) ^ 130 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_943105868581 : Nat.Prime 943105868581 := by
  apply lucas_primality 943105868581 (10 : ZMod 943105868581)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (2677, 1), (202471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (2677, 1), (202471, 1)] : List FactorBlock).map factorBlockValue).prod) = 943105868581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_2677
      · exact prime_ninetySixCP_202471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 943105868581) ^ 471552934290 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 943105868581) ^ 314368622860 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 943105868581) ^ 188621173716 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 943105868581) ^ 32520892020 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 943105868581) ^ 352299540 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 943105868581) ^ 4657980 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1010114293753 : Nat.Prime 1010114293753 := by
  apply lucas_primality 1010114293753 (5 : ZMod 1010114293753)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (14029365191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (14029365191, 1)] : List FactorBlock).map factorBlockValue).prod) = 1010114293753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_14029365191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1010114293753) ^ 505057146876 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010114293753) ^ 336704764584 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1010114293753) ^ 72 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1018998619013 : Nat.Prime 1018998619013 := by
  apply lucas_primality 1018998619013 (2 : ZMod 1018998619013)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (1362297619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (1362297619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1018998619013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_1362297619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1018998619013) ^ 509499309506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018998619013) ^ 92636238092 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018998619013) ^ 59941095236 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018998619013) ^ 748 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1056724570063 : Nat.Prime 1056724570063 := by
  apply lucas_primality 1056724570063 (3 : ZMod 1056724570063)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (127, 1), (2277139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (127, 1), (2277139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1056724570063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_127
      · exact prime_ninetySixCP_2277139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1056724570063) ^ 528362285031 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1056724570063) ^ 352241523354 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1056724570063) ^ 150960652866 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1056724570063) ^ 36438778278 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1056724570063) ^ 8320665906 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1056724570063) ^ 464058 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1403958862931 : Nat.Prime 1403958862931 := by
  apply lucas_primality 1403958862931 (2 : ZMod 1403958862931)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (10799683561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (10799683561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403958862931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_10799683561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1403958862931) ^ 701979431465 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403958862931) ^ 280791772586 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403958862931) ^ 107996835610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403958862931) ^ 130 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1544207075809 : Nat.Prime 1544207075809 := by
  apply lucas_primality 1544207075809 (11 : ZMod 1544207075809)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (239, 1), (6053, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (239, 1), (6053, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1544207075809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_239
      · exact prime_ninetySixCP_6053
      · exact prime_ninetySixCP_11119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1544207075809) ^ 772103537904 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1544207075809) ^ 514735691936 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1544207075809) ^ 6461117472 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1544207075809) ^ 255114336 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 1544207075809) ^ 138880032 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1678883593609 : Nat.Prime 1678883593609 := by
  apply lucas_primality 1678883593609 (14 : ZMod 1678883593609)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (53, 1), (83, 1), (407747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (53, 1), (83, 1), (407747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678883593609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_407747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1678883593609) ^ 839441796804 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 1678883593609) ^ 559627864536 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 1678883593609) ^ 129144891816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 1678883593609) ^ 31677048936 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 1678883593609) ^ 20227513176 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (14 : ZMod 1678883593609) ^ 4117464 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1832592512117 : Nat.Prime 1832592512117 := by
  apply lucas_primality 1832592512117 (2 : ZMod 1832592512117)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1171, 1), (391245199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1171, 1), (391245199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1832592512117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_1171
      · exact prime_ninetySixCP_391245199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1832592512117) ^ 916296256058 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1832592512117) ^ 1564980796 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1832592512117) ^ 4684 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3085735391183 : Nat.Prime 3085735391183 := by
  apply lucas_primality 3085735391183 (5 : ZMod 3085735391183)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2971, 1), (519309221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2971, 1), (519309221, 1)] : List FactorBlock).map factorBlockValue).prod) = 3085735391183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_2971
      · exact prime_ninetySixCP_519309221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3085735391183) ^ 1542867695591 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3085735391183) ^ 1038618442 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3085735391183) ^ 5942 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3134855077363 : Nat.Prime 3134855077363 := by
  apply lucas_primality 3134855077363 (3 : ZMod 3134855077363)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (3943, 1), (241361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (3943, 1), (241361, 1)] : List FactorBlock).map factorBlockValue).prod) = 3134855077363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_61
      · exact prime_ninetySixCP_3943
      · exact prime_ninetySixCP_241361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3134855077363) ^ 1567427538681 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3134855077363) ^ 1044951692454 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3134855077363) ^ 51391066842 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3134855077363) ^ 795043134 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3134855077363) ^ 12988242 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3621693869533 : Nat.Prime 3621693869533 := by
  apply lucas_primality 3621693869533 (2 : ZMod 3621693869533)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (223, 1), (451132769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (223, 1), (451132769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3621693869533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_223
      · exact prime_ninetySixCP_451132769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3621693869533) ^ 1810846934766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3621693869533) ^ 1207231289844 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3621693869533) ^ 16240779684 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3621693869533) ^ 8028 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3769223515567 : Nat.Prime 3769223515567 := by
  apply lucas_primality 3769223515567 (3 : ZMod 3769223515567)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (11852904137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (11852904137, 1)] : List FactorBlock).map factorBlockValue).prod) = 3769223515567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_11852904137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3769223515567) ^ 1884611757783 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3769223515567) ^ 1256407838522 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3769223515567) ^ 71117424822 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 3769223515567) ^ 318 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3915290957891 : Nat.Prime 3915290957891 := by
  apply lucas_primality 3915290957891 (2 : ZMod 3915290957891)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (30117622753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (30117622753, 1)] : List FactorBlock).map factorBlockValue).prod) = 3915290957891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_30117622753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3915290957891) ^ 1957645478945 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3915290957891) ^ 783058191578 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3915290957891) ^ 301176227530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3915290957891) ^ 130 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_4819129534129 : Nat.Prime 4819129534129 := by
  apply lucas_primality 4819129534129 (19 : ZMod 4819129534129)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (13, 1), (83, 1), (2339, 1), (5683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (13, 1), (83, 1), (2339, 1), (5683, 1)] : List FactorBlock).map factorBlockValue).prod) = 4819129534129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_2339
      · exact prime_ninetySixCP_5683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4819129534129) ^ 2409564767064 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 1606376511376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 688447076304 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 370702271856 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 58061801616 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 2060337552 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (19 : ZMod 4819129534129) ^ 847990416 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6127864952003 : Nat.Prime 6127864952003 := by
  apply lucas_primality 6127864952003 (2 : ZMod 6127864952003)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (349, 1), (4657, 1), (35569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (349, 1), (4657, 1), (35569, 1)] : List FactorBlock).map factorBlockValue).prod) = 6127864952003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_349
      · exact prime_ninetySixCP_4657
      · exact prime_ninetySixCP_35569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6127864952003) ^ 3063932476001 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6127864952003) ^ 115620093434 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6127864952003) ^ 17558352298 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6127864952003) ^ 1315839586 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6127864952003) ^ 172281058 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6274887299579 : Nat.Prime 6274887299579 := by
  apply lucas_primality 6274887299579 (2 : ZMod 6274887299579)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (33751, 1), (731957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (33751, 1), (731957, 1)] : List FactorBlock).map factorBlockValue).prod) = 6274887299579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_127
      · exact prime_ninetySixCP_33751
      · exact prime_ninetySixCP_731957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6274887299579) ^ 3137443649789 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6274887299579) ^ 49408561414 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6274887299579) ^ 185917078 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6274887299579) ^ 8572754 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6474099371503 : Nat.Prime 6474099371503 := by
  apply lucas_primality 6474099371503 (3 : ZMod 6474099371503)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (61, 1), (109, 1), (23183219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (61, 1), (109, 1), (23183219, 1)] : List FactorBlock).map factorBlockValue).prod) = 6474099371503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_61
      · exact prime_ninetySixCP_109
      · exact prime_ninetySixCP_23183219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6474099371503) ^ 3237049685751 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6474099371503) ^ 2158033123834 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6474099371503) ^ 924871338786 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6474099371503) ^ 106132776582 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6474099371503) ^ 59395407078 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6474099371503) ^ 279258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_7264023006067 : Nat.Prime 7264023006067 := by
  apply lucas_primality 7264023006067 (3 : ZMod 7264023006067)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (84229, 1), (14373559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (84229, 1), (14373559, 1)] : List FactorBlock).map factorBlockValue).prod) = 7264023006067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_84229
      · exact prime_ninetySixCP_14373559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7264023006067) ^ 3632011503033 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7264023006067) ^ 2421341002022 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7264023006067) ^ 86241354 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7264023006067) ^ 505374 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_7388348564981 : Nat.Prime 7388348564981 := by
  apply lucas_primality 7388348564981 (2 : ZMod 7388348564981)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (823, 1), (448866863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (823, 1), (448866863, 1)] : List FactorBlock).map factorBlockValue).prod) = 7388348564981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_823
      · exact prime_ninetySixCP_448866863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7388348564981) ^ 3694174282490 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7388348564981) ^ 1477669712996 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7388348564981) ^ 8977337260 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7388348564981) ^ 16460 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_9083372145479 : Nat.Prime 9083372145479 := by
  apply lucas_primality 9083372145479 (7 : ZMod 9083372145479)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (44967188839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (44967188839, 1)] : List FactorBlock).map factorBlockValue).prod) = 9083372145479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_44967188839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 9083372145479) ^ 4541686072739 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9083372145479) ^ 89934377678 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 9083372145479) ^ 202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_9715659535867 : Nat.Prime 9715659535867 := by
  apply lucas_primality 9715659535867 (2 : ZMod 9715659535867)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (86249, 1), (18774439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (86249, 1), (18774439, 1)] : List FactorBlock).map factorBlockValue).prod) = 9715659535867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_86249
      · exact prime_ninetySixCP_18774439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9715659535867) ^ 4857829767933 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9715659535867) ^ 3238553178622 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9715659535867) ^ 112646634 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9715659535867) ^ 517494 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_16965557405191 : Nat.Prime 16965557405191 := by
  apply lucas_primality 16965557405191 (13 : ZMod 16965557405191)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7121, 1), (2941319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7121, 1), (2941319, 1)] : List FactorBlock).map factorBlockValue).prod) = 16965557405191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7121
      · exact prime_ninetySixCP_2941319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 16965557405191) ^ 8482778702595 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 16965557405191) ^ 5655185801730 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 16965557405191) ^ 3393111481038 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 16965557405191) ^ 2382468390 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 16965557405191) ^ 5768010 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_17789317715597 : Nat.Prime 17789317715597 := by
  apply lucas_primality 17789317715597 (2 : ZMod 17789317715597)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (635332775557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (635332775557, 1)] : List FactorBlock).map factorBlockValue).prod) = 17789317715597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_635332775557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17789317715597) ^ 8894658857798 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17789317715597) ^ 2541331102228 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17789317715597) ^ 28 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_23256164021221 : Nat.Prime 23256164021221 := by
  apply lucas_primality 23256164021221 (2 : ZMod 23256164021221)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (97, 1), (587, 1), (7589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (97, 1), (587, 1), (7589, 1)] : List FactorBlock).map factorBlockValue).prod) = 23256164021221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_97
      · exact prime_ninetySixCP_587
      · exact prime_ninetySixCP_7589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23256164021221) ^ 11628082010610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 7752054673740 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 4651232804244 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 1788935693940 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 1011137566140 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 239754268260 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 39618678060 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 23256164021221) ^ 3064456980 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_24173636860507 : Nat.Prime 24173636860507 := by
  apply lucas_primality 24173636860507 (2 : ZMod 24173636860507)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (575562782393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (575562782393, 1)] : List FactorBlock).map factorBlockValue).prod) = 24173636860507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_575562782393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24173636860507) ^ 12086818430253 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24173636860507) ^ 8057878953502 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24173636860507) ^ 3453376694358 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24173636860507) ^ 42 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_25351648984303 : Nat.Prime 25351648984303 := by
  apply lucas_primality 25351648984303 (3 : ZMod 25351648984303)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5857, 1), (721405981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5857, 1), (721405981, 1)] : List FactorBlock).map factorBlockValue).prod) = 25351648984303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5857
      · exact prime_ninetySixCP_721405981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25351648984303) ^ 12675824492151 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 25351648984303) ^ 8450549661434 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 25351648984303) ^ 4328435886 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 25351648984303) ^ 35142 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_27688066298917 : Nat.Prime 27688066298917 := by
  apply lucas_primality 27688066298917 (2 : ZMod 27688066298917)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2393, 1), (3461, 1), (278591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2393, 1), (3461, 1), (278591, 1)] : List FactorBlock).map factorBlockValue).prod) = 27688066298917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2393
      · exact prime_ninetySixCP_3461
      · exact prime_ninetySixCP_278591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27688066298917) ^ 13844033149458 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27688066298917) ^ 9229355432972 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27688066298917) ^ 11570441412 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27688066298917) ^ 8000019156 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 27688066298917) ^ 99386076 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_34238418068341 : Nat.Prime 34238418068341 := by
  apply lucas_primality 34238418068341 (2 : ZMod 34238418068341)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (449, 1), (423637937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (449, 1), (423637937, 1)] : List FactorBlock).map factorBlockValue).prod) = 34238418068341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_449
      · exact prime_ninetySixCP_423637937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34238418068341) ^ 17119209034170 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34238418068341) ^ 11412806022780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34238418068341) ^ 6847683613668 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34238418068341) ^ 76254828660 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34238418068341) ^ 80820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35283593052359 : Nat.Prime 35283593052359 := by
  apply lucas_primality 35283593052359 (7 : ZMod 35283593052359)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (23, 1), (439, 1), (13137079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (23, 1), (439, 1), (13137079, 1)] : List FactorBlock).map factorBlockValue).prod) = 35283593052359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_439
      · exact prime_ninetySixCP_13137079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35283593052359) ^ 17641796526179 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 35283593052359) ^ 5040513293194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 35283593052359) ^ 1857031213282 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 35283593052359) ^ 1534069263146 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 35283593052359) ^ 80372649322 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 35283593052359) ^ 2685802 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_37124362878023 : Nat.Prime 37124362878023 := by
  apply lucas_primality 37124362878023 (5 : ZMod 37124362878023)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (15031, 1), (2990137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (15031, 1), (2990137, 1)] : List FactorBlock).map factorBlockValue).prod) = 37124362878023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_15031
      · exact prime_ninetySixCP_2990137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37124362878023) ^ 18562181439011 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 37124362878023) ^ 5303480411146 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 37124362878023) ^ 629226489458 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 37124362878023) ^ 2469853162 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 37124362878023) ^ 12415606 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_48596747331373 : Nat.Prime 48596747331373 := by
  apply lucas_primality 48596747331373 (5 : ZMod 48596747331373)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (101, 1), (6421, 1), (132863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (101, 1), (6421, 1), (132863, 1)] : List FactorBlock).map factorBlockValue).prod) = 48596747331373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_47
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_6421
      · exact prime_ninetySixCP_132863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48596747331373) ^ 24298373665686 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48596747331373) ^ 16198915777124 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48596747331373) ^ 1033973347476 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48596747331373) ^ 481155914172 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48596747331373) ^ 7568407932 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48596747331373) ^ 365765844 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_72232293977497 : Nat.Prime 72232293977497 := by
  apply lucas_primality 72232293977497 (5 : ZMod 72232293977497)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (613, 1), (1636584511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (613, 1), (1636584511, 1)] : List FactorBlock).map factorBlockValue).prod) = 72232293977497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_613
      · exact prime_ninetySixCP_1636584511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 72232293977497) ^ 36116146988748 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 72232293977497) ^ 24077431325832 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 72232293977497) ^ 117834084792 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 72232293977497) ^ 44136 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_76216186002911 : Nat.Prime 76216186002911 := by
  apply lucas_primality 76216186002911 (11 : ZMod 76216186002911)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (347299, 1), (21945409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (347299, 1), (21945409, 1)] : List FactorBlock).map factorBlockValue).prod) = 76216186002911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_347299
      · exact prime_ninetySixCP_21945409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 76216186002911) ^ 38108093001455 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 76216186002911) ^ 15243237200582 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 76216186002911) ^ 219454090 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 76216186002911) ^ 3472990 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_88358384849101 : Nat.Prime 88358384849101 := by
  apply lucas_primality 88358384849101 (7 : ZMod 88358384849101)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (294527949497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (294527949497, 1)] : List FactorBlock).map factorBlockValue).prod) = 88358384849101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_294527949497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 88358384849101) ^ 44179192424550 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 88358384849101) ^ 29452794949700 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 88358384849101) ^ 17671676969820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 88358384849101) ^ 300 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_92571911580241 : Nat.Prime 92571911580241 := by
  apply lucas_primality 92571911580241 (13 : ZMod 92571911580241)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (97, 1), (1031, 1), (55897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (97, 1), (1031, 1), (55897, 1)] : List FactorBlock).map factorBlockValue).prod) = 92571911580241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_97
      · exact prime_ninetySixCP_1031
      · exact prime_ninetySixCP_55897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 92571911580241) ^ 46285955790120 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 30857303860080 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 18514382316048 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 4024865720880 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 954349603920 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 89788469040 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 92571911580241) ^ 1656115920 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_133047730135687 : Nat.Prime 133047730135687 := by
  apply lucas_primality 133047730135687 (3 : ZMod 133047730135687)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (11681, 1), (35817917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (11681, 1), (35817917, 1)] : List FactorBlock).map factorBlockValue).prod) = 133047730135687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_11681
      · exact prime_ninetySixCP_35817917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133047730135687) ^ 66523865067843 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 133047730135687) ^ 44349243378562 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 133047730135687) ^ 2510334530862 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 133047730135687) ^ 11390097606 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 133047730135687) ^ 3714558 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_141026221863157 : Nat.Prime 141026221863157 := by
  apply lucas_primality 141026221863157 (5 : ZMod 141026221863157)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1678883593609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1678883593609, 1)] : List FactorBlock).map factorBlockValue).prod) = 141026221863157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_1678883593609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 141026221863157) ^ 70513110931578 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 141026221863157) ^ 47008740621052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 141026221863157) ^ 20146603123308 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 141026221863157) ^ 84 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_194730199891901 : Nat.Prime 194730199891901 := by
  apply lucas_primality 194730199891901 (2 : ZMod 194730199891901)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (2153, 1), (53203519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (2153, 1), (53203519, 1)] : List FactorBlock).map factorBlockValue).prod) = 194730199891901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_2153
      · exact prime_ninetySixCP_53203519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 194730199891901) ^ 97365099945950 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194730199891901) ^ 38946039978380 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194730199891901) ^ 11454717640700 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194730199891901) ^ 90445982300 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 194730199891901) ^ 3660100 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_205639126574971 : Nat.Prime 205639126574971 := by
  apply lucas_primality 205639126574971 (3 : ZMod 205639126574971)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (623148868409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (623148868409, 1)] : List FactorBlock).map factorBlockValue).prod) = 205639126574971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_623148868409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 205639126574971) ^ 102819563287485 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 205639126574971) ^ 68546375524990 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 205639126574971) ^ 41127825314994 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 205639126574971) ^ 18694466052270 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 205639126574971) ^ 330 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_209634811505261 : Nat.Prime 209634811505261 := by
  apply lucas_primality 209634811505261 (3 : ZMod 209634811505261)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (140321, 1), (74698303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (140321, 1), (74698303, 1)] : List FactorBlock).map factorBlockValue).prod) = 209634811505261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_140321
      · exact prime_ninetySixCP_74698303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 209634811505261) ^ 104817405752630 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 209634811505261) ^ 41926962301052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 209634811505261) ^ 1493966060 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 209634811505261) ^ 2806420 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_293365480323607 : Nat.Prime 293365480323607 := by
  apply lucas_primality 293365480323607 (3 : ZMod 293365480323607)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (226871, 1), (215515631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (226871, 1), (215515631, 1)] : List FactorBlock).map factorBlockValue).prod) = 293365480323607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_226871
      · exact prime_ninetySixCP_215515631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 293365480323607) ^ 146682740161803 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 293365480323607) ^ 97788493441202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 293365480323607) ^ 1293093786 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 293365480323607) ^ 1361226 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_347071207810879 : Nat.Prime 347071207810879 := by
  apply lucas_primality 347071207810879 (3 : ZMod 347071207810879)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (941, 1), (20490684131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (941, 1), (20490684131, 1)] : List FactorBlock).map factorBlockValue).prod) = 347071207810879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_941
      · exact prime_ninetySixCP_20490684131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 347071207810879) ^ 173535603905439 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 347071207810879) ^ 115690402603626 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 347071207810879) ^ 368832314358 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 347071207810879) ^ 16938 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_636141750025871 : Nat.Prime 636141750025871 := by
  apply lucas_primality 636141750025871 (11 : ZMod 636141750025871)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (53, 1), (19379, 1), (5630591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (53, 1), (19379, 1), (5630591, 1)] : List FactorBlock).map factorBlockValue).prod) = 636141750025871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_53
      · exact prime_ninetySixCP_19379
      · exact prime_ninetySixCP_5630591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 636141750025871) ^ 318070875012935 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 636141750025871) ^ 127228350005174 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 636141750025871) ^ 57831068184170 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 636141750025871) ^ 12002674528790 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 636141750025871) ^ 32826345530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 636141750025871) ^ 112979570 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_752407594548179 : Nat.Prime 752407594548179 := by
  apply lucas_primality 752407594548179 (2 : ZMod 752407594548179)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (37, 1), (61, 1), (67, 1), (130937249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (37, 1), (61, 1), (67, 1), (130937249, 1)] : List FactorBlock).map factorBlockValue).prod) = 752407594548179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_61
      · exact prime_ninetySixCP_67
      · exact prime_ninetySixCP_130937249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 752407594548179) ^ 376203797274089 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752407594548179) ^ 39600399713062 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752407594548179) ^ 20335340393194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752407594548179) ^ 12334550730298 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752407594548179) ^ 11229964097734 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752407594548179) ^ 5746322 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_823019386416217 : Nat.Prime 823019386416217 := by
  apply lucas_primality 823019386416217 (5 : ZMod 823019386416217)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (67, 1), (15671, 1), (2969167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (67, 1), (15671, 1), (2969167, 1)] : List FactorBlock).map factorBlockValue).prod) = 823019386416217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_67
      · exact prime_ninetySixCP_15671
      · exact prime_ninetySixCP_2969167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 823019386416217) ^ 411509693208108 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 823019386416217) ^ 274339795472072 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 823019386416217) ^ 74819944219656 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 823019386416217) ^ 12283871439048 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 823019386416217) ^ 52518625896 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 823019386416217) ^ 277188648 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_883583848491011 : Nat.Prime 883583848491011 := by
  apply lucas_primality 883583848491011 (13 : ZMod 883583848491011)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (88358384849101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (88358384849101, 1)] : List FactorBlock).map factorBlockValue).prod) = 883583848491011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_88358384849101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 883583848491011) ^ 441791924245505 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 883583848491011) ^ 176716769698202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (13 : ZMod 883583848491011) ^ 10 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_914594232034933 : Nat.Prime 914594232034933 := by
  apply lucas_primality 914594232034933 (2 : ZMod 914594232034933)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (76216186002911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (76216186002911, 1)] : List FactorBlock).map factorBlockValue).prod) = 914594232034933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_76216186002911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 914594232034933) ^ 457297116017466 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 914594232034933) ^ 304864744011644 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 914594232034933) ^ 12 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1174587287367301 : Nat.Prime 1174587287367301 := by
  apply lucas_primality 1174587287367301 (2 : ZMod 1174587287367301)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (3915290957891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (3915290957891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1174587287367301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_3915290957891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1174587287367301) ^ 587293643683650 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174587287367301) ^ 391529095789100 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174587287367301) ^ 234917457473460 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1174587287367301) ^ 300 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1411912629146717 : Nat.Prime 1411912629146717 := by
  apply lucas_primality 1411912629146717 (2 : ZMod 1411912629146717)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (152783, 1), (2310323513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (152783, 1), (2310323513, 1)] : List FactorBlock).map factorBlockValue).prod) = 1411912629146717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_152783
      · exact prime_ninetySixCP_2310323513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1411912629146717) ^ 705956314573358 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1411912629146717) ^ 9241294052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1411912629146717) ^ 611132 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1419929684623837 : Nat.Prime 1419929684623837 := by
  apply lucas_primality 1419929684623837 (6 : ZMod 1419929684623837)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (912871, 1), (2541593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (912871, 1), (2541593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1419929684623837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_912871
      · exact prime_ninetySixCP_2541593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1419929684623837) ^ 709964842311918 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1419929684623837) ^ 473309894874612 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1419929684623837) ^ 83525275566108 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1419929684623837) ^ 1555454916 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1419929684623837) ^ 558677052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1505583582468943 : Nat.Prime 1505583582468943 := by
  apply lucas_primality 1505583582468943 (3 : ZMod 1505583582468943)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15137, 1), (16577300461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15137, 1), (16577300461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1505583582468943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_15137
      · exact prime_ninetySixCP_16577300461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1505583582468943) ^ 752791791234471 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505583582468943) ^ 501861194156314 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505583582468943) ^ 99463802766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1505583582468943) ^ 90822 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1641606068218687 : Nat.Prime 1641606068218687 := by
  apply lucas_primality 1641606068218687 (5 : ZMod 1641606068218687)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (127, 1), (196477, 1), (296347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (127, 1), (196477, 1), (296347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1641606068218687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_127
      · exact prime_ninetySixCP_196477
      · exact prime_ninetySixCP_296347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1641606068218687) ^ 820803034109343 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1641606068218687) ^ 547202022739562 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1641606068218687) ^ 44367731573478 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1641606068218687) ^ 12926032033218 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1641606068218687) ^ 8355207318 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1641606068218687) ^ 5539472538 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2394859142442367 : Nat.Prime 2394859142442367 := by
  apply lucas_primality 2394859142442367 (3 : ZMod 2394859142442367)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (133047730135687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (133047730135687, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394859142442367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_133047730135687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2394859142442367) ^ 1197429571221183 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2394859142442367) ^ 798286380814122 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2394859142442367) ^ 18 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2540832266907899 : Nat.Prime 2540832266907899 := by
  apply lucas_primality 2540832266907899 (2 : ZMod 2540832266907899)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13687, 1), (92819181227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13687, 1), (92819181227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2540832266907899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13687
      · exact prime_ninetySixCP_92819181227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2540832266907899) ^ 1270416133453949 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540832266907899) ^ 185638362454 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540832266907899) ^ 27374 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3405376269410579 : Nat.Prime 3405376269410579 := by
  apply lucas_primality 3405376269410579 (2 : ZMod 3405376269410579)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (263, 1), (6474099371503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (263, 1), (6474099371503, 1)] : List FactorBlock).map factorBlockValue).prod) = 3405376269410579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_263
      · exact prime_ninetySixCP_6474099371503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3405376269410579) ^ 1702688134705289 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3405376269410579) ^ 12948198743006 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3405376269410579) ^ 526 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_3677122073530021 : Nat.Prime 3677122073530021 := by
  apply lucas_primality 3677122073530021 (2 : ZMod 3677122073530021)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (347, 1), (176614893061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (347, 1), (176614893061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3677122073530021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_347
      · exact prime_ninetySixCP_176614893061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3677122073530021) ^ 1838561036765010 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3677122073530021) ^ 1225707357843340 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3677122073530021) ^ 735424414706004 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3677122073530021) ^ 10596893583660 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3677122073530021) ^ 20820 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_4937499360646313 : Nat.Prime 4937499360646313 := by
  apply lucas_primality 4937499360646313 (3 : ZMod 4937499360646313)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (41047, 1), (140524441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (41047, 1), (140524441, 1)] : List FactorBlock).map factorBlockValue).prod) = 4937499360646313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_41047
      · exact prime_ninetySixCP_140524441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4937499360646313) ^ 2468749680323156 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4937499360646313) ^ 46144853837816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4937499360646313) ^ 120288921496 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 4937499360646313) ^ 35136232 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5862185563261711 : Nat.Prime 5862185563261711 := by
  apply lucas_primality 5862185563261711 (3 : ZMod 5862185563261711)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (269, 1), (17717488933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (269, 1), (17717488933, 1)] : List FactorBlock).map factorBlockValue).prod) = 5862185563261711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_269
      · exact prime_ninetySixCP_17717488933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5862185563261711) ^ 2931092781630855 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5862185563261711) ^ 1954061854420570 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5862185563261711) ^ 1172437112652342 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5862185563261711) ^ 142980135689310 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5862185563261711) ^ 21792511387590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5862185563261711) ^ 330870 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6485755241806129 : Nat.Prime 6485755241806129 := by
  apply lucas_primality 6485755241806129 (37 : ZMod 6485755241806129)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (4444339, 1), (10134233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (4444339, 1), (10134233, 1)] : List FactorBlock).map factorBlockValue).prod) = 6485755241806129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_4444339
      · exact prime_ninetySixCP_10134233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 6485755241806129) ^ 3242877620903064 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (37 : ZMod 6485755241806129) ^ 2161918413935376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (37 : ZMod 6485755241806129) ^ 1459329552 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (37 : ZMod 6485755241806129) ^ 639984816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_10301270560942313 : Nat.Prime 10301270560942313 := by
  apply lucas_primality 10301270560942313 (5 : ZMod 10301270560942313)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (67, 1), (101, 1), (1599033893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (67, 1), (101, 1), (1599033893, 1)] : List FactorBlock).map factorBlockValue).prod) = 10301270560942313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_67
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_1599033893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10301270560942313) ^ 5150635280471156 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10301270560942313) ^ 1471610080134616 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10301270560942313) ^ 605957091820136 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10301270560942313) ^ 153750306879736 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10301270560942313) ^ 101992777831112 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 10301270560942313) ^ 6442184 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_14369154854654203 : Nat.Prime 14369154854654203 := by
  apply lucas_primality 14369154854654203 (2 : ZMod 14369154854654203)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2394859142442367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2394859142442367, 1)] : List FactorBlock).map factorBlockValue).prod) = 14369154854654203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_2394859142442367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14369154854654203) ^ 7184577427327101 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369154854654203) ^ 4789718284884734 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14369154854654203) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_15895681685495783 : Nat.Prime 15895681685495783 := by
  apply lucas_primality 15895681685495783 (5 : ZMod 15895681685495783)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1297, 1), (6127864952003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1297, 1), (6127864952003, 1)] : List FactorBlock).map factorBlockValue).prod) = 15895681685495783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_1297
      · exact prime_ninetySixCP_6127864952003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15895681685495783) ^ 7947840842747891 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15895681685495783) ^ 12255729904006 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15895681685495783) ^ 2594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_16198408427898289 : Nat.Prime 16198408427898289 := by
  apply lucas_primality 16198408427898289 (11 : ZMod 16198408427898289)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (131, 1), (4447, 1), (579285533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (131, 1), (4447, 1), (579285533, 1)] : List FactorBlock).map factorBlockValue).prod) = 16198408427898289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_131
      · exact prime_ninetySixCP_4447
      · exact prime_ninetySixCP_579285533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 16198408427898289) ^ 8099204213949144 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 16198408427898289) ^ 5399469475966096 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 16198408427898289) ^ 123651972732048 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 16198408427898289) ^ 3642547431504 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 16198408427898289) ^ 27962736 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_18726861170693119 : Nat.Prime 18726861170693119 := by
  apply lucas_primality 18726861170693119 (6 : ZMod 18726861170693119)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (5693, 1), (1785805603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (5693, 1), (1785805603, 1)] : List FactorBlock).map factorBlockValue).prod) = 18726861170693119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_307
      · exact prime_ninetySixCP_5693
      · exact prime_ninetySixCP_1785805603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18726861170693119) ^ 9363430585346559 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18726861170693119) ^ 6242287056897706 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18726861170693119) ^ 60999547787274 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18726861170693119) ^ 3289453920726 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18726861170693119) ^ 10486506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_20500373706264643 : Nat.Prime 20500373706264643 := by
  apply lucas_primality 20500373706264643 (2 : ZMod 20500373706264643)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2551, 1), (78786380221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2551, 1), (78786380221, 1)] : List FactorBlock).map factorBlockValue).prod) = 20500373706264643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_2551
      · exact prime_ninetySixCP_78786380221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20500373706264643) ^ 10250186853132321 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20500373706264643) ^ 6833457902088214 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20500373706264643) ^ 1205904335662626 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20500373706264643) ^ 8036210782542 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 20500373706264643) ^ 260202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_23078167599836273 : Nat.Prime 23078167599836273 := by
  apply lucas_primality 23078167599836273 (3 : ZMod 23078167599836273)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (163, 1), (114921956417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (163, 1), (114921956417, 1)] : List FactorBlock).map factorBlockValue).prod) = 23078167599836273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_163
      · exact prime_ninetySixCP_114921956417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23078167599836273) ^ 11539083799918136 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078167599836273) ^ 3296881085690896 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078167599836273) ^ 2098015236348752 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078167599836273) ^ 141583850305744 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 23078167599836273) ^ 200816 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_26319043548298307 : Nat.Prime 26319043548298307 := by
  apply lucas_primality 26319043548298307 (2 : ZMod 26319043548298307)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (34337, 1), (29480470213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (34337, 1), (29480470213, 1)] : List FactorBlock).map factorBlockValue).prod) = 26319043548298307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_34337
      · exact prime_ninetySixCP_29480470213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26319043548298307) ^ 13159521774149153 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26319043548298307) ^ 2024541811407562 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26319043548298307) ^ 766492225538 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26319043548298307) ^ 892762 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_26367922070537711 : Nat.Prime 26367922070537711 := by
  apply lucas_primality 26367922070537711 (11 : ZMod 26367922070537711)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (4483, 1), (33073, 1), (1368013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (4483, 1), (33073, 1), (1368013, 1)] : List FactorBlock).map factorBlockValue).prod) = 26367922070537711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_4483
      · exact prime_ninetySixCP_33073
      · exact prime_ninetySixCP_1368013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 26367922070537711) ^ 13183961035268855 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 26367922070537711) ^ 5273584414107542 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 26367922070537711) ^ 2028301697733670 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 26367922070537711) ^ 5881758213370 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 26367922070537711) ^ 797264296270 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 26367922070537711) ^ 19274613670 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_43080386241022969 : Nat.Prime 43080386241022969 := by
  apply lucas_primality 43080386241022969 (7 : ZMod 43080386241022969)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (135799, 1), (13218183443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (135799, 1), (13218183443, 1)] : List FactorBlock).map factorBlockValue).prod) = 43080386241022969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_135799
      · exact prime_ninetySixCP_13218183443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 43080386241022969) ^ 21540193120511484 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43080386241022969) ^ 14360128747007656 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43080386241022969) ^ 317236402632 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 43080386241022969) ^ 3259176 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_46156335199672547 : Nat.Prime 46156335199672547 := by
  apply lucas_primality 46156335199672547 (2 : ZMod 46156335199672547)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23078167599836273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23078167599836273, 1)] : List FactorBlock).map factorBlockValue).prod) = 46156335199672547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_23078167599836273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 46156335199672547) ^ 23078167599836273 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46156335199672547) ^ 2 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_121934571091759519 : Nat.Prime 121934571091759519 := by
  apply lucas_primality 121934571091759519 (3 : ZMod 121934571091759519)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (883583848491011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (883583848491011, 1)] : List FactorBlock).map factorBlockValue).prod) = 121934571091759519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_883583848491011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121934571091759519) ^ 60967285545879759 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121934571091759519) ^ 40644857030586506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121934571091759519) ^ 5301503090946066 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 121934571091759519) ^ 138 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_189486711894345347 : Nat.Prime 189486711894345347 := by
  apply lucas_primality 189486711894345347 (2 : ZMod 189486711894345347)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (179, 1), (1403958862931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (179, 1), (1403958862931, 1)] : List FactorBlock).map factorBlockValue).prod) = 189486711894345347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_179
      · exact prime_ninetySixCP_1403958862931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 189486711894345347) ^ 94743355947172673 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 189486711894345347) ^ 14575900914949642 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 189486711894345347) ^ 6534024548080874 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 189486711894345347) ^ 1058584982649974 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 189486711894345347) ^ 134966 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_193633369236474197 : Nat.Prime 193633369236474197 := by
  apply lucas_primality 193633369236474197 (2 : ZMod 193633369236474197)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79691, 1), (607450556639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79691, 1), (607450556639, 1)] : List FactorBlock).map factorBlockValue).prod) = 193633369236474197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_79691
      · exact prime_ninetySixCP_607450556639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 193633369236474197) ^ 96816684618237098 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 193633369236474197) ^ 2429802226556 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 193633369236474197) ^ 318764 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_202899251273634791 : Nat.Prime 202899251273634791 := by
  apply lucas_primality 202899251273634791 (7 : ZMod 202899251273634791)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (24967, 1), (16585096513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (24967, 1), (16585096513, 1)] : List FactorBlock).map factorBlockValue).prod) = 202899251273634791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_24967
      · exact prime_ninetySixCP_16585096513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 202899251273634791) ^ 101449625636817395 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 202899251273634791) ^ 40579850254726958 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 202899251273634791) ^ 28985607324804970 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 202899251273634791) ^ 8126697291370 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 202899251273634791) ^ 12233830 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_234151881951025333 : Nat.Prime 234151881951025333 := by
  apply lucas_primality 234151881951025333 (2 : ZMod 234151881951025333)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (17, 1), (43633, 1), (1252659731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (17, 1), (43633, 1), (1252659731, 1)] : List FactorBlock).map factorBlockValue).prod) = 234151881951025333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_43633
      · exact prime_ninetySixCP_1252659731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 234151881951025333) ^ 117075940975512666 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 234151881951025333) ^ 78050627317008444 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 234151881951025333) ^ 33450268850146476 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 234151881951025333) ^ 13773640114766196 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 234151881951025333) ^ 5366394287604 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 234151881951025333) ^ 186923772 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_237266632048194803 : Nat.Prime 237266632048194803 := by
  apply lucas_primality 237266632048194803 (2 : ZMod 237266632048194803)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (1174587287367301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (1174587287367301, 1)] : List FactorBlock).map factorBlockValue).prod) = 237266632048194803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_1174587287367301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 237266632048194803) ^ 118633316024097401 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237266632048194803) ^ 2349174574734602 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 237266632048194803) ^ 202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_241681426008181283 : Nat.Prime 241681426008181283 := by
  apply lucas_primality 241681426008181283 (2 : ZMod 241681426008181283)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (183848377, 1), (657284633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (183848377, 1), (657284633, 1)] : List FactorBlock).map factorBlockValue).prod) = 241681426008181283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_183848377
      · exact prime_ninetySixCP_657284633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 241681426008181283) ^ 120840713004090641 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 241681426008181283) ^ 1314569266 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 241681426008181283) ^ 367696754 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_338809461494812151 : Nat.Prime 338809461494812151 := by
  apply lucas_primality 338809461494812151 (7 : ZMod 338809461494812151)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1871, 1), (3621693869533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1871, 1), (3621693869533, 1)] : List FactorBlock).map factorBlockValue).prod) = 338809461494812151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_1871
      · exact prime_ninetySixCP_3621693869533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 338809461494812151) ^ 169404730747406075 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 338809461494812151) ^ 67761892298962430 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 338809461494812151) ^ 181084693476650 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 338809461494812151) ^ 93550 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_369250681597380377 : Nat.Prime 369250681597380377 := by
  apply lucas_primality 369250681597380377 (3 : ZMod 369250681597380377)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (46156335199672547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (46156335199672547, 1)] : List FactorBlock).map factorBlockValue).prod) = 369250681597380377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_46156335199672547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 369250681597380377) ^ 184625340798690188 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 369250681597380377) ^ 8 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_426642362611698889 : Nat.Prime 426642362611698889 := by
  apply lucas_primality 426642362611698889 (11 : ZMod 426642362611698889)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (73, 1), (405529, 1), (4882057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (73, 1), (405529, 1), (4882057, 1)] : List FactorBlock).map factorBlockValue).prod) = 426642362611698889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_73
      · exact prime_ninetySixCP_405529
      · exact prime_ninetySixCP_4882057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 426642362611698889) ^ 213321181305849444 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 426642362611698889) ^ 142214120870566296 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 426642362611698889) ^ 10405911283212168 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 426642362611698889) ^ 5844415926187656 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 426642362611698889) ^ 1052063755272 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 426642362611698889) ^ 87389877384 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_477418189122235027 : Nat.Prime 477418189122235027 := by
  apply lucas_primality 477418189122235027 (2 : ZMod 477418189122235027)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (914594232034933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (914594232034933, 1)] : List FactorBlock).map factorBlockValue).prod) = 477418189122235027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_914594232034933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 477418189122235027) ^ 238709094561117513 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 477418189122235027) ^ 159139396374078342 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 477418189122235027) ^ 16462696176628794 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 477418189122235027) ^ 522 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_782652116068132087 : Nat.Prime 782652116068132087 := by
  apply lucas_primality 782652116068132087 (3 : ZMod 782652116068132087)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (23, 1), (647, 1), (139137708727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (23, 1), (647, 1), (139137708727, 1)] : List FactorBlock).map factorBlockValue).prod) = 782652116068132087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_647
      · exact prime_ninetySixCP_139137708727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 782652116068132087) ^ 391326058034066043 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 782652116068132087) ^ 260884038689377362 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 782652116068132087) ^ 111807445152590298 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 782652116068132087) ^ 34028352872527482 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 782652116068132087) ^ 1209663239672538 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 782652116068132087) ^ 5625018 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_941273469264486779 : Nat.Prime 941273469264486779 := by
  apply lucas_primality 941273469264486779 (2 : ZMod 941273469264486779)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (107, 1), (544177, 1), (1154685793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (107, 1), (544177, 1), (1154685793, 1)] : List FactorBlock).map factorBlockValue).prod) = 941273469264486779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_107
      · exact prime_ninetySixCP_544177
      · exact prime_ninetySixCP_1154685793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 941273469264486779) ^ 470636734632243389 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 941273469264486779) ^ 134467638466355254 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 941273469264486779) ^ 8796948310883054 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 941273469264486779) ^ 1729719317914 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 941273469264486779) ^ 815177146 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1432992535954288759 : Nat.Prime 1432992535954288759 := by
  apply lucas_primality 1432992535954288759 (6 : ZMod 1432992535954288759)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (32237, 1), (33829372631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (32237, 1), (33829372631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432992535954288759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_73
      · exact prime_ninetySixCP_32237
      · exact prime_ninetySixCP_33829372631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1432992535954288759) ^ 716496267977144379 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432992535954288759) ^ 477664178651429586 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432992535954288759) ^ 19630034739099846 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432992535954288759) ^ 44451795637134 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1432992535954288759) ^ 42359418 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2666419522326260399 : Nat.Prime 2666419522326260399 := by
  apply lucas_primality 2666419522326260399 (17 : ZMod 2666419522326260399)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1693, 1), (34238418068341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1693, 1), (34238418068341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2666419522326260399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_23
      · exact prime_ninetySixCP_1693
      · exact prime_ninetySixCP_34238418068341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2666419522326260399) ^ 1333209761163130199 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 2666419522326260399) ^ 115931283579402626 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 2666419522326260399) ^ 1574967231143686 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 2666419522326260399) ^ 77878 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_4568768806019049923 : Nat.Prime 4568768806019049923 := by
  apply lucas_primality 4568768806019049923 (2 : ZMod 4568768806019049923)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57139, 1), (2223269, 1), (17982271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57139, 1), (2223269, 1), (17982271, 1)] : List FactorBlock).map factorBlockValue).prod) = 4568768806019049923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_57139
      · exact prime_ninetySixCP_2223269
      · exact prime_ninetySixCP_17982271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4568768806019049923) ^ 2284384403009524961 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4568768806019049923) ^ 79958851327798 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4568768806019049923) ^ 2054977965338 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4568768806019049923) ^ 254070734782 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5060866997781252103 : Nat.Prime 5060866997781252103 := by
  apply lucas_primality 5060866997781252103 (6 : ZMod 5060866997781252103)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5981, 1), (141026221863157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5981, 1), (141026221863157, 1)] : List FactorBlock).map factorBlockValue).prod) = 5060866997781252103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5981
      · exact prime_ninetySixCP_141026221863157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5060866997781252103) ^ 2530433498890626051 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 5060866997781252103) ^ 1686955665927084034 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 5060866997781252103) ^ 846157331178942 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 5060866997781252103) ^ 35886 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6419362999541336123 : Nat.Prime 6419362999541336123 := by
  apply lucas_primality 6419362999541336123 (2 : ZMod 6419362999541336123)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (3299, 1), (170759, 1), (21024551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (3299, 1), (170759, 1), (21024551, 1)] : List FactorBlock).map factorBlockValue).prod) = 6419362999541336123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_271
      · exact prime_ninetySixCP_3299
      · exact prime_ninetySixCP_170759
      · exact prime_ninetySixCP_21024551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6419362999541336123) ^ 3209681499770668061 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6419362999541336123) ^ 23687686345170982 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6419362999541336123) ^ 1945851166881278 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6419362999541336123) ^ 37593116611958 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6419362999541336123) ^ 305326996022 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6662857903170299903 : Nat.Prime 6662857903170299903 := by
  apply lucas_primality 6662857903170299903 (5 : ZMod 6662857903170299903)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (4723, 1), (37124362878023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (4723, 1), (37124362878023, 1)] : List FactorBlock).map factorBlockValue).prod) = 6662857903170299903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_4723
      · exact prime_ninetySixCP_37124362878023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6662857903170299903) ^ 3331428951585149951 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6662857903170299903) ^ 350676731745805258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6662857903170299903) ^ 1410725789364874 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6662857903170299903) ^ 179474 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_10117391994920452157 : Nat.Prime 10117391994920452157 := by
  apply lucas_primality 10117391994920452157 (2 : ZMod 10117391994920452157)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (14841737, 1), (628860857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (14841737, 1), (628860857, 1)] : List FactorBlock).map factorBlockValue).prod) = 10117391994920452157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_271
      · exact prime_ninetySixCP_14841737
      · exact prime_ninetySixCP_628860857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10117391994920452157) ^ 5058695997460226078 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10117391994920452157) ^ 37333549796754436 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10117391994920452157) ^ 681685168988 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10117391994920452157) ^ 16088442908 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_13590725572567983337 : Nat.Prime 13590725572567983337 := by
  apply lucas_primality 13590725572567983337 (5 : ZMod 13590725572567983337)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (43, 1), (193, 1), (953, 1), (10228564691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (43, 1), (193, 1), (953, 1), (10228564691, 1)] : List FactorBlock).map factorBlockValue).prod) = 13590725572567983337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_43
      · exact prime_ninetySixCP_193
      · exact prime_ninetySixCP_953
      · exact prime_ninetySixCP_10228564691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13590725572567983337) ^ 6795362786283991668 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 4530241857522661112 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 1941532224652569048 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 316063385408557752 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 70418267215378152 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 14260992206262312 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 13590725572567983337) ^ 1328703096 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_27755813050601942513 : Nat.Prime 27755813050601942513 := by
  apply lucas_primality 27755813050601942513 (3 : ZMod 27755813050601942513)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (1429, 1), (4674253, 1), (7019203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (1429, 1), (4674253, 1), (7019203, 1)] : List FactorBlock).map factorBlockValue).prod) = 27755813050601942513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_1429
      · exact prime_ninetySixCP_4674253
      · exact prime_ninetySixCP_7019203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27755813050601942513) ^ 13877906525300971256 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 27755813050601942513) ^ 750157109475728176 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 27755813050601942513) ^ 19423242162772528 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 27755813050601942513) ^ 5938021123504 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 27755813050601942513) ^ 3954268461904 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_28323448509335454731 : Nat.Prime 28323448509335454731 := by
  apply lucas_primality 28323448509335454731 (2 : ZMod 28323448509335454731)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15541, 1), (6682097, 1), (27274349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15541, 1), (6682097, 1), (27274349, 1)] : List FactorBlock).map factorBlockValue).prod) = 28323448509335454731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_15541
      · exact prime_ninetySixCP_6682097
      · exact prime_ninetySixCP_27274349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28323448509335454731) ^ 14161724254667727365 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28323448509335454731) ^ 5664689701867090946 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28323448509335454731) ^ 1822498456298530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28323448509335454731) ^ 4238706578090 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 28323448509335454731) ^ 1038464694770 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_32682898142084217809 : Nat.Prime 32682898142084217809 := by
  apply lucas_primality 32682898142084217809 (3 : ZMod 32682898142084217809)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (4675859, 1), (3610387367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (4675859, 1), (3610387367, 1)] : List FactorBlock).map factorBlockValue).prod) = 32682898142084217809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_4675859
      · exact prime_ninetySixCP_3610387367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32682898142084217809) ^ 16341449071042108904 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32682898142084217809) ^ 2971172558371292528 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32682898142084217809) ^ 6989709942512 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 32682898142084217809) ^ 9052463024 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35674189783843168177 : Nat.Prime 35674189783843168177 := by
  apply lucas_primality 35674189783843168177 (5 : ZMod 35674189783843168177)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1933, 1), (1162367, 1), (330778867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1933, 1), (1162367, 1), (330778867, 1)] : List FactorBlock).map factorBlockValue).prod) = 35674189783843168177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_1933
      · exact prime_ninetySixCP_1162367
      · exact prime_ninetySixCP_330778867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 35674189783843168177) ^ 17837094891921584088 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 35674189783843168177) ^ 11891396594614389392 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 35674189783843168177) ^ 18455349086313072 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 35674189783843168177) ^ 30690986395728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 35674189783843168177) ^ 107849059728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35688623051492504293 : Nat.Prime 35688623051492504293 := by
  apply lucas_primality 35688623051492504293 (2 : ZMod 35688623051492504293)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (26319043548298307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (26319043548298307, 1)] : List FactorBlock).map factorBlockValue).prod) = 35688623051492504293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_113
      · exact prime_ninetySixCP_26319043548298307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35688623051492504293) ^ 17844311525746252146 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35688623051492504293) ^ 11896207683830834764 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35688623051492504293) ^ 315828522579579684 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35688623051492504293) ^ 1356 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_35691448957840156661 : Nat.Prime 35691448957840156661 := by
  apply lucas_primality 35691448957840156661 (2 : ZMod 35691448957840156661)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (461, 1), (38933, 1), (965335247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (461, 1), (38933, 1), (965335247, 1)] : List FactorBlock).map factorBlockValue).prod) = 35691448957840156661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_103
      · exact prime_ninetySixCP_461
      · exact prime_ninetySixCP_38933
      · exact prime_ninetySixCP_965335247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35691448957840156661) ^ 17845724478920078330 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35691448957840156661) ^ 7138289791568031332 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35691448957840156661) ^ 346518921920778220 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35691448957840156661) ^ 77421798173189060 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35691448957840156661) ^ 916740270666020 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35691448957840156661) ^ 36973112780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_51981717793127623927 : Nat.Prime 51981717793127623927 := by
  apply lucas_primality 51981717793127623927 (3 : ZMod 51981717793127623927)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (234151881951025333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (234151881951025333, 1)] : List FactorBlock).map factorBlockValue).prod) = 51981717793127623927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_234151881951025333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51981717793127623927) ^ 25990858896563811963 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51981717793127623927) ^ 17327239264375874642 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51981717793127623927) ^ 1404911291706151998 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 51981717793127623927) ^ 222 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_52263004626865246831 : Nat.Prime 52263004626865246831 := by
  apply lucas_primality 52263004626865246831 (3 : ZMod 52263004626865246831)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (37, 1), (443, 1), (5441, 1), (253687003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (37, 1), (443, 1), (5441, 1), (253687003, 1)] : List FactorBlock).map factorBlockValue).prod) = 52263004626865246831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_443
      · exact prime_ninetySixCP_5441
      · exact prime_ninetySixCP_253687003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52263004626865246831) ^ 26131502313432623415 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 17421001542288415610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 10452600925373049366 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 7466143518123606690 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 4751182238805931530 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 1412513638563925590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 117975179744616810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 9605404268859630 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 52263004626865246831) ^ 206013725610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_63113162929673314517 : Nat.Prime 63113162929673314517 := by
  apply lucas_primality 63113162929673314517 (2 : ZMod 63113162929673314517)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (227, 1), (241, 1), (16965557405191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (227, 1), (241, 1), (16965557405191, 1)] : List FactorBlock).map factorBlockValue).prod) = 63113162929673314517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_227
      · exact prime_ninetySixCP_241
      · exact prime_ninetySixCP_16965557405191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63113162929673314517) ^ 31556581464836657258 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63113162929673314517) ^ 3712538995863136148 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63113162929673314517) ^ 278031554756270108 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63113162929673314517) ^ 261880344106528276 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63113162929673314517) ^ 3720076 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_117641475010767428639 : Nat.Prime 117641475010767428639 := by
  apply lucas_primality 117641475010767428639 (7 : ZMod 117641475010767428639)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12289, 1), (80909, 1), (59158491019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12289, 1), (80909, 1), (59158491019, 1)] : List FactorBlock).map factorBlockValue).prod) = 117641475010767428639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_12289
      · exact prime_ninetySixCP_80909
      · exact prime_ninetySixCP_59158491019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 117641475010767428639) ^ 58820737505383714319 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 117641475010767428639) ^ 9572908699712542 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 117641475010767428639) ^ 1453997392264982 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 117641475010767428639) ^ 1988581402 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_117940805426403893077 : Nat.Prime 117940805426403893077 := by
  apply lucas_primality 117940805426403893077 (2 : ZMod 117940805426403893077)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (17, 1), (83, 1), (433, 1), (21499, 1), (5232553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (17, 1), (83, 1), (433, 1), (21499, 1), (5232553, 1)] : List FactorBlock).map factorBlockValue).prod) = 117940805426403893077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_83
      · exact prime_ninetySixCP_433
      · exact prime_ninetySixCP_21499
      · exact prime_ninetySixCP_5232553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117940805426403893077) ^ 58970402713201946538 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 39313601808801297692 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 10721891402400353916 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 9072369648184914852 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 6937694436847287828 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 1420973559354263772 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 272380612994004372 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 5485874013972924 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 117940805426403893077) ^ 22539820509492 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_205742047130728249811 : Nat.Prime 205742047130728249811 := by
  apply lucas_primality 205742047130728249811 (2 : ZMod 205742047130728249811)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (101, 1), (967, 1), (7264023006067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (101, 1), (967, 1), (7264023006067, 1)] : List FactorBlock).map factorBlockValue).prod) = 205742047130728249811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_101
      · exact prime_ninetySixCP_967
      · exact prime_ninetySixCP_7264023006067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 205742047130728249811) ^ 102871023565364124905 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205742047130728249811) ^ 41148409426145649962 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205742047130728249811) ^ 7094553349335456890 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205742047130728249811) ^ 2037049971591368810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205742047130728249811) ^ 212763233847702430 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 205742047130728249811) ^ 28323430 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_223139730834113900497 : Nat.Prime 223139730834113900497 := by
  apply lucas_primality 223139730834113900497 (5 : ZMod 223139730834113900497)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (35803, 1), (287783, 1), (451181323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (35803, 1), (287783, 1), (451181323, 1)] : List FactorBlock).map factorBlockValue).prod) = 223139730834113900497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_35803
      · exact prime_ninetySixCP_287783
      · exact prime_ninetySixCP_451181323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 223139730834113900497) ^ 111569865417056950248 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 223139730834113900497) ^ 74379910278037966832 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 223139730834113900497) ^ 6232431104491632 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 223139730834113900497) ^ 775374955553712 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 223139730834113900497) ^ 494567747952 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_311890306758765743563 : Nat.Prime 311890306758765743563 := by
  apply lucas_primality 311890306758765743563 (5 : ZMod 311890306758765743563)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (51981717793127623927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (51981717793127623927, 1)] : List FactorBlock).map factorBlockValue).prod) = 311890306758765743563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_51981717793127623927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 311890306758765743563) ^ 155945153379382871781 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 311890306758765743563) ^ 103963435586255247854 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 311890306758765743563) ^ 6 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_377595970568877627181 : Nat.Prime 377595970568877627181 := by
  apply lucas_primality 377595970568877627181 (17 : ZMod 377595970568877627181)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (313, 1), (86461, 1), (2500509797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (313, 1), (86461, 1), (2500509797, 1)] : List FactorBlock).map factorBlockValue).prod) = 377595970568877627181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_31
      · exact prime_ninetySixCP_313
      · exact prime_ninetySixCP_86461
      · exact prime_ninetySixCP_2500509797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 377595970568877627181) ^ 188797985284438813590 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 125865323522959209060 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 75519194113775525436 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 12180515179641213780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 1206376902775966860 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 4367240380852380 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (17 : ZMod 377595970568877627181) ^ 151007594940 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_411572520599612710049 : Nat.Prime 411572520599612710049 := by
  apply lucas_primality 411572520599612710049 (3 : ZMod 411572520599612710049)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6373, 1), (15535111, 1), (129908663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6373, 1), (15535111, 1), (129908663, 1)] : List FactorBlock).map factorBlockValue).prod) = 411572520599612710049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_6373
      · exact prime_ninetySixCP_15535111
      · exact prime_ninetySixCP_129908663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 411572520599612710049) ^ 205786260299806355024 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 411572520599612710049) ^ 64580655986130976 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 411572520599612710049) ^ 26493053097568 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 411572520599612710049) ^ 3168168396896 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_426622070183391314359 : Nat.Prime 426622070183391314359 := by
  apply lucas_primality 426622070183391314359 (6 : ZMod 426622070183391314359)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (85199, 1), (6274887299579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (85199, 1), (6274887299579, 1)] : List FactorBlock).map factorBlockValue).prod) = 426622070183391314359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_85199
      · exact prime_ninetySixCP_6274887299579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 426622070183391314359) ^ 213311035091695657179 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 426622070183391314359) ^ 142207356727797104786 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 426622070183391314359) ^ 60946010026198759194 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 426622070183391314359) ^ 22453793167546911282 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 426622070183391314359) ^ 5007360065064042 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 426622070183391314359) ^ 67988802 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_455183441002800295417 : Nat.Prime 455183441002800295417 := by
  apply lucas_primality 455183441002800295417 (10 : ZMod 455183441002800295417)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (43, 1), (1979, 1), (197641, 1), (125297213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (43, 1), (1979, 1), (197641, 1), (125297213, 1)] : List FactorBlock).map factorBlockValue).prod) = 455183441002800295417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_43
      · exact prime_ninetySixCP_1979
      · exact prime_ninetySixCP_197641
      · exact prime_ninetySixCP_125297213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 455183441002800295417) ^ 227591720501400147708 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 455183441002800295417) ^ 151727813667600098472 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 455183441002800295417) ^ 10585661418669774312 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 455183441002800295417) ^ 230006791815462504 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 455183441002800295417) ^ 2303082057886776 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 455183441002800295417) ^ 3632829734232 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_651089761666040376403 : Nat.Prime 651089761666040376403 := by
  apply lucas_primality 651089761666040376403 (2 : ZMod 651089761666040376403)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (241681426008181283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (241681426008181283, 1)] : List FactorBlock).map factorBlockValue).prod) = 651089761666040376403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_449
      · exact prime_ninetySixCP_241681426008181283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 651089761666040376403) ^ 325544880833020188201 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 651089761666040376403) ^ 217029920555346792134 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 651089761666040376403) ^ 1450088556049087698 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 651089761666040376403) ^ 2694 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1098404363153633149051 : Nat.Prime 1098404363153633149051 := by
  apply lucas_primality 1098404363153633149051 (3 : ZMod 1098404363153633149051)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (109, 1), (229, 1), (293365480323607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (109, 1), (229, 1), (293365480323607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1098404363153633149051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_109
      · exact prime_ninetySixCP_229
      · exact prime_ninetySixCP_293365480323607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1098404363153633149051) ^ 549202181576816574525 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098404363153633149051) ^ 366134787717877716350 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098404363153633149051) ^ 219680872630726629810 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098404363153633149051) ^ 10077104249115900450 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098404363153633149051) ^ 4796525603290974450 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098404363153633149051) ^ 3744150 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_4114840942614564996221 : Nat.Prime 4114840942614564996221 := by
  apply lucas_primality 4114840942614564996221 (2 : ZMod 4114840942614564996221)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (205742047130728249811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (205742047130728249811, 1)] : List FactorBlock).map factorBlockValue).prod) = 4114840942614564996221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_205742047130728249811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4114840942614564996221) ^ 2057420471307282498110 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4114840942614564996221) ^ 822968188522912999244 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4114840942614564996221) ^ 20 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6421132183834415731543 : Nat.Prime 6421132183834415731543 := by
  apply lucas_primality 6421132183834415731543 (3 : ZMod 6421132183834415731543)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103889, 1), (10301270560942313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103889, 1), (10301270560942313, 1)] : List FactorBlock).map factorBlockValue).prod) = 6421132183834415731543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_103889
      · exact prime_ninetySixCP_10301270560942313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6421132183834415731543) ^ 3210566091917207865771 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6421132183834415731543) ^ 2140377394611471910514 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6421132183834415731543) ^ 61807623365653878 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6421132183834415731543) ^ 623334 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_14081602908820262260909 : Nat.Prime 14081602908820262260909 := by
  apply lucas_primality 14081602908820262260909 (6 : ZMod 14081602908820262260909)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73823, 1), (15895681685495783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73823, 1), (15895681685495783, 1)] : List FactorBlock).map factorBlockValue).prod) = 14081602908820262260909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_73823
      · exact prime_ninetySixCP_15895681685495783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14081602908820262260909) ^ 7040801454410131130454 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 14081602908820262260909) ^ 4693867636273420753636 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 14081602908820262260909) ^ 190748180225949396 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 14081602908820262260909) ^ 885876 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_14158332000493362981347 : Nat.Prime 14158332000493362981347 := by
  apply lucas_primality 14158332000493362981347 (2 : ZMod 14158332000493362981347)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25453, 1), (1170857, 1), (237541372813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25453, 1), (1170857, 1), (237541372813, 1)] : List FactorBlock).map factorBlockValue).prod) = 14158332000493362981347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_25453
      · exact prime_ninetySixCP_1170857
      · exact prime_ninetySixCP_237541372813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14158332000493362981347) ^ 7079166000246681490673 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14158332000493362981347) ^ 556253958295421482 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14158332000493362981347) ^ 12092281124418578 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 14158332000493362981347) ^ 59603646442 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_15949254293337098290793 : Nat.Prime 15949254293337098290793 := by
  apply lucas_primality 15949254293337098290793 (3 : ZMod 15949254293337098290793)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (32682898142084217809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (32682898142084217809, 1)] : List FactorBlock).map factorBlockValue).prod) = 15949254293337098290793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_61
      · exact prime_ninetySixCP_32682898142084217809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15949254293337098290793) ^ 7974627146668549145396 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15949254293337098290793) ^ 261463185136673742472 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 15949254293337098290793) ^ 488 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_29918427969511283986423 : Nat.Prime 29918427969511283986423 := by
  apply lucas_primality 29918427969511283986423 (5 : ZMod 29918427969511283986423)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (102611, 1), (16198408427898289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (102611, 1), (16198408427898289, 1)] : List FactorBlock).map factorBlockValue).prod) = 29918427969511283986423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_102611
      · exact prime_ninetySixCP_16198408427898289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29918427969511283986423) ^ 14959213984755641993211 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 29918427969511283986423) ^ 9972809323170427995474 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 29918427969511283986423) ^ 291571351702169202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 29918427969511283986423) ^ 1846998 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_39254495122611807474313 : Nat.Prime 39254495122611807474313 := by
  apply lucas_primality 39254495122611807474313 (7 : ZMod 39254495122611807474313)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (61, 1), (163, 1), (727, 1), (3539, 1), (21312013699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (61, 1), (163, 1), (727, 1), (3539, 1), (21312013699, 1)] : List FactorBlock).map factorBlockValue).prod) = 39254495122611807474313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_61
      · exact prime_ninetySixCP_163
      · exact prime_ninetySixCP_727
      · exact prime_ninetySixCP_3539
      · exact prime_ninetySixCP_21312013699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39254495122611807474313) ^ 19627247561305903737156 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 13084831707537269158104 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 643516313485439466792 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 240825123451606180824 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 53995178985710876856 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 11091973756036114008 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 39254495122611807474313) ^ 1841895171288 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_95359564238717258494607 : Nat.Prime 95359564238717258494607 := by
  apply lucas_primality 95359564238717258494607 (5 : ZMod 95359564238717258494607)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (59380471, 1), (27688066298917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (59380471, 1), (27688066298917, 1)] : List FactorBlock).map factorBlockValue).prod) = 95359564238717258494607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_59380471
      · exact prime_ninetySixCP_27688066298917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95359564238717258494607) ^ 47679782119358629247303 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95359564238717258494607) ^ 3288260835817836499814 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95359564238717258494607) ^ 1605907845337186 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 95359564238717258494607) ^ 3444067318 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_246305600854754670314867 : Nat.Prime 246305600854754670314867 := by
  apply lucas_primality 246305600854754670314867 (2 : ZMod 246305600854754670314867)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (103, 1), (541, 1), (3405376269410579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (103, 1), (541, 1), (3405376269410579, 1)] : List FactorBlock).map factorBlockValue).prod) = 246305600854754670314867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_59
      · exact prime_ninetySixCP_103
      · exact prime_ninetySixCP_541
      · exact prime_ninetySixCP_3405376269410579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 246305600854754670314867) ^ 123152800427377335157433 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 246305600854754670314867) ^ 22391418259523151846806 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 246305600854754670314867) ^ 4174671200928045259574 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 246305600854754670314867) ^ 2391316513152957964222 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 246305600854754670314867) ^ 455278374962577948826 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 246305600854754670314867) ^ 72328454 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_334471703023778790457457 : Nat.Prime 334471703023778790457457 := by
  apply lucas_primality 334471703023778790457457 (3 : ZMod 334471703023778790457457)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (426622070183391314359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (426622070183391314359, 1)] : List FactorBlock).map factorBlockValue).prod) = 334471703023778790457457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_426622070183391314359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 334471703023778790457457) ^ 167235851511889395228728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 334471703023778790457457) ^ 47781671860539827208208 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 334471703023778790457457) ^ 784 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_378621990138511674415261 : Nat.Prime 378621990138511674415261 := by
  apply lucas_primality 378621990138511674415261 (6 : ZMod 378621990138511674415261)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (164449, 1), (752407594548179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (164449, 1), (752407594548179, 1)] : List FactorBlock).map factorBlockValue).prod) = 378621990138511674415261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_164449
      · exact prime_ninetySixCP_752407594548179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 378621990138511674415261) ^ 189310995069255837207630 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 378621990138511674415261) ^ 126207330046170558138420 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 378621990138511674415261) ^ 75724398027702334883052 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 378621990138511674415261) ^ 22271881772853627906780 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 378621990138511674415261) ^ 2302367239317427740 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 378621990138511674415261) ^ 503213940 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_471053941471341689691757 : Nat.Prime 471053941471341689691757 := by
  apply lucas_primality 471053941471341689691757 (5 : ZMod 471053941471341689691757)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (39254495122611807474313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (39254495122611807474313, 1)] : List FactorBlock).map factorBlockValue).prod) = 471053941471341689691757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_39254495122611807474313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 471053941471341689691757) ^ 235526970735670844845878 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 471053941471341689691757) ^ 157017980490447229897252 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 471053941471341689691757) ^ 12 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_478602118855509530416501 : Nat.Prime 478602118855509530416501 := by
  apply lucas_primality 478602118855509530416501 (11 : ZMod 478602118855509530416501)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (7, 1), (79, 1), (269, 1), (10069, 1), (213019620067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (7, 1), (79, 1), (269, 1), (10069, 1), (213019620067, 1)] : List FactorBlock).map factorBlockValue).prod) = 478602118855509530416501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_79
      · exact prime_ninetySixCP_269
      · exact prime_ninetySixCP_10069
      · exact prime_ninetySixCP_213019620067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 478602118855509530416501) ^ 239301059427754765208250 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 159534039618503176805500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 95720423771101906083300 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 68371731265072790059500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 6058254669057082663500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 1779190032920109778500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 47532239433460078500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 478602118855509530416501) ^ 2246751349500 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_509485704356849256768629 : Nat.Prime 509485704356849256768629 := by
  apply lucas_primality 509485704356849256768629 (2 : ZMod 509485704356849256768629)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (353, 1), (27755813050601942513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (353, 1), (27755813050601942513, 1)] : List FactorBlock).map factorBlockValue).prod) = 509485704356849256768629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_353
      · exact prime_ninetySixCP_27755813050601942513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 509485704356849256768629) ^ 254742852178424628384314 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 509485704356849256768629) ^ 39191208027449942828356 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 509485704356849256768629) ^ 1443302278631301010676 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 509485704356849256768629) ^ 18356 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_925815884183885996485013 : Nat.Prime 925815884183885996485013 := by
  apply lucas_primality 925815884183885996485013 (2 : ZMod 925815884183885996485013)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2500261333, 1), (92571911580241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2500261333, 1), (92571911580241, 1)] : List FactorBlock).map factorBlockValue).prod) = 925815884183885996485013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_2500261333
      · exact prime_ninetySixCP_92571911580241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 925815884183885996485013) ^ 462907942091942998242506 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 925815884183885996485013) ^ 370287646320964 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 925815884183885996485013) ^ 10001045332 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5195112412407696804187793 : Nat.Prime 5195112412407696804187793 := by
  apply lucas_primality 5195112412407696804187793 (3 : ZMod 5195112412407696804187793)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (41, 1), (2837, 1), (31307, 1), (670407215531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (41, 1), (2837, 1), (31307, 1), (670407215531, 1)] : List FactorBlock).map factorBlockValue).prod) = 5195112412407696804187793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_2837
      · exact prime_ninetySixCP_31307
      · exact prime_ninetySixCP_670407215531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5195112412407696804187793) ^ 2597556206203848402093896 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 742158916058242400598256 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 273426969074089305483568 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 126710058839212117175312 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 1831199299403488475216 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 165940920957220327856 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 5195112412407696804187793) ^ 7749189286832 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5231751676678849086433609 : Nat.Prime 5231751676678849086433609 := by
  apply lucas_primality 5231751676678849086433609 (7 : ZMod 5231751676678849086433609)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (109, 1), (117641475010767428639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (109, 1), (117641475010767428639, 1)] : List FactorBlock).map factorBlockValue).prod) = 5231751676678849086433609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_109
      · exact prime_ninetySixCP_117641475010767428639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5231751676678849086433609) ^ 2615875838339424543216804 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 5231751676678849086433609) ^ 1743917225559616362144536 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 5231751676678849086433609) ^ 307750098628167593319624 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 5231751676678849086433609) ^ 47997721804393110884712 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 5231751676678849086433609) ^ 44472 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_6948124938712638633675587 : Nat.Prime 6948124938712638633675587 := by
  apply lucas_primality 6948124938712638633675587 (2 : ZMod 6948124938712638633675587)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15569, 1), (223139730834113900497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15569, 1), (223139730834113900497, 1)] : List FactorBlock).map factorBlockValue).prod) = 6948124938712638633675587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_15569
      · exact prime_ninetySixCP_223139730834113900497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6948124938712638633675587) ^ 3474062469356319316837793 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6948124938712638633675587) ^ 446279461668227800994 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6948124938712638633675587) ^ 31138 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_7536863063541467035068113 : Nat.Prime 7536863063541467035068113 := by
  apply lucas_primality 7536863063541467035068113 (3 : ZMod 7536863063541467035068113)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (471053941471341689691757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (471053941471341689691757, 1)] : List FactorBlock).map factorBlockValue).prod) = 7536863063541467035068113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_471053941471341689691757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7536863063541467035068113) ^ 3768431531770733517534056 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 7536863063541467035068113) ^ 16 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_21697117353062693955475189 : Nat.Prime 21697117353062693955475189 := by
  apply lucas_primality 21697117353062693955475189 (10 : ZMod 21697117353062693955475189)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (7237, 1), (35691448957840156661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (7237, 1), (35691448957840156661, 1)] : List FactorBlock).map factorBlockValue).prod) = 21697117353062693955475189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_7237
      · exact prime_ninetySixCP_35691448957840156661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21697117353062693955475189) ^ 10848558676531346977737594 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21697117353062693955475189) ^ 7232372451020897985158396 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21697117353062693955475189) ^ 3099588193294670565067884 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21697117353062693955475189) ^ 2998081712458573159524 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (10 : ZMod 21697117353062693955475189) ^ 607908 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_30249898953590339040802429 : Nat.Prime 30249898953590339040802429 := by
  apply lucas_primality 30249898953590339040802429 (2 : ZMod 30249898953590339040802429)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (37, 1), (2633, 1), (3342263, 1), (368663535043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (37, 1), (2633, 1), (3342263, 1), (368663535043, 1)] : List FactorBlock).map factorBlockValue).prod) = 30249898953590339040802429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_37
      · exact prime_ninetySixCP_2633
      · exact prime_ninetySixCP_3342263
      · exact prime_ninetySixCP_368663535043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30249898953590339040802429) ^ 15124949476795169520401214 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 10083299651196779680267476 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 4321414136227191291543204 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 817564836583522676778444 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 11488757673220789609116 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 9050723702350873956 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30249898953590339040802429) ^ 82052864138196 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_31448495670233015262147607 : Nat.Prime 31448495670233015262147607 := by
  apply lucas_primality 31448495670233015262147607 (3 : ZMod 31448495670233015262147607)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (14328493, 1), (121934571091759519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (14328493, 1), (121934571091759519, 1)] : List FactorBlock).map factorBlockValue).prod) = 31448495670233015262147607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_14328493
      · exact prime_ninetySixCP_121934571091759519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31448495670233015262147607) ^ 15724247835116507631073803 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448495670233015262147607) ^ 10482831890077671754049202 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448495670233015262147607) ^ 2194822279651671342 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31448495670233015262147607) ^ 257912874 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_47608062447093520168242749 : Nat.Prime 47608062447093520168242749 := by
  apply lucas_primality 47608062447093520168242749 (2 : ZMod 47608062447093520168242749)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (333631, 1), (35674189783843168177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (333631, 1), (35674189783843168177, 1)] : List FactorBlock).map factorBlockValue).prod) = 47608062447093520168242749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_333631
      · exact prime_ninetySixCP_35674189783843168177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47608062447093520168242749) ^ 23804031223546760084121374 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47608062447093520168242749) ^ 142696759135372672708 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 47608062447093520168242749) ^ 1334524 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_102250108895379236109090733 : Nat.Prime 102250108895379236109090733 := by
  apply lucas_primality 102250108895379236109090733 (2 : ZMod 102250108895379236109090733)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1327, 1), (6421132183834415731543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1327, 1), (6421132183834415731543, 1)] : List FactorBlock).map factorBlockValue).prod) = 102250108895379236109090733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_1327
      · exact prime_ninetySixCP_6421132183834415731543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102250108895379236109090733) ^ 51125054447689618054545366 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 102250108895379236109090733) ^ 34083369631793078703030244 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 102250108895379236109090733) ^ 77053586206012988778516 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 102250108895379236109090733) ^ 15924 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_235472242476910688964918493 : Nat.Prime 235472242476910688964918493 := by
  apply lucas_primality 235472242476910688964918493 (5 : ZMod 235472242476910688964918493)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (478602118855509530416501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (478602118855509530416501, 1)] : List FactorBlock).map factorBlockValue).prod) = 235472242476910688964918493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_478602118855509530416501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 235472242476910688964918493) ^ 117736121238455344482459246 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 235472242476910688964918493) ^ 78490747492303562988306164 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 235472242476910688964918493) ^ 5743225426266114364998012 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 235472242476910688964918493) ^ 492 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_285888213788088040506525727 : Nat.Prime 285888213788088040506525727 := by
  apply lucas_primality 285888213788088040506525727 (3 : ZMod 285888213788088040506525727)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (887, 1), (1061, 1), (11953, 1), (1411912629146717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (887, 1), (1061, 1), (11953, 1), (1411912629146717, 1)] : List FactorBlock).map factorBlockValue).prod) = 285888213788088040506525727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_887
      · exact prime_ninetySixCP_1061
      · exact prime_ninetySixCP_11953
      · exact prime_ninetySixCP_1411912629146717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 285888213788088040506525727) ^ 142944106894044020253262863 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 285888213788088040506525727) ^ 95296071262696013502175242 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 285888213788088040506525727) ^ 322309147449930147132498 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 285888213788088040506525727) ^ 269451662382740848733766 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 285888213788088040506525727) ^ 23917695456210829122942 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 285888213788088040506525727) ^ 202482935478 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_502201862273765274695091653 : Nat.Prime 502201862273765274695091653 := by
  apply lucas_primality 502201862273765274695091653 (2 : ZMod 502201862273765274695091653)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (24697, 1), (26106029, 1), (194730199891901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (24697, 1), (26106029, 1), (194730199891901, 1)] : List FactorBlock).map factorBlockValue).prod) = 502201862273765274695091653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_24697
      · exact prime_ninetySixCP_26106029
      · exact prime_ninetySixCP_194730199891901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 502201862273765274695091653) ^ 251100931136882637347545826 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 502201862273765274695091653) ^ 20334528982215057484516 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 502201862273765274695091653) ^ 19237006986921115988 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 502201862273765274695091653) ^ 2578962392852 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_603710749329100808941971881 : Nat.Prime 603710749329100808941971881 := by
  apply lucas_primality 603710749329100808941971881 (6 : ZMod 603710749329100808941971881)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (13, 2), (17, 1), (499, 1), (1223, 1), (16603, 1), (44357, 1), (1669781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (13, 2), (17, 1), (499, 1), (1223, 1), (16603, 1), (44357, 1), (1669781, 1)] : List FactorBlock).map factorBlockValue).prod) = 603710749329100808941971881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_13
      · exact prime_ninetySixCP_17
      · exact prime_ninetySixCP_499
      · exact prime_ninetySixCP_1223
      · exact prime_ninetySixCP_16603
      · exact prime_ninetySixCP_44357
      · exact prime_ninetySixCP_1669781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 603710749329100808941971881) ^ 301855374664550404470985940 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 120742149865820161788394376 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 86244392761300115563138840 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 46439288409930831457074760 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 35512397019358871114233640 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 1209841181020242102088120 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 493631029704906630369560 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 36361546065717087811960 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 13610270066260135016840 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 603710749329100808941971881) ^ 361550855668558217480 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1004403724547530549390183307 : Nat.Prime 1004403724547530549390183307 := by
  apply lucas_primality 1004403724547530549390183307 (2 : ZMod 1004403724547530549390183307)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (502201862273765274695091653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (502201862273765274695091653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1004403724547530549390183307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_502201862273765274695091653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1004403724547530549390183307) ^ 502201862273765274695091653 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1004403724547530549390183307) ^ 2 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1233669792107292957403159931 : Nat.Prime 1233669792107292957403159931 := by
  apply lucas_primality 1233669792107292957403159931 (6 : ZMod 1233669792107292957403159931)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (283, 1), (439, 1), (52263004626865246831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (283, 1), (439, 1), (52263004626865246831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1233669792107292957403159931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_283
      · exact prime_ninetySixCP_439
      · exact prime_ninetySixCP_52263004626865246831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1233669792107292957403159931) ^ 616834896053646478701579965 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1233669792107292957403159931) ^ 246733958421458591480631986 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1233669792107292957403159931) ^ 64929989058278576705429470 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1233669792107292957403159931) ^ 4359257215926830238173710 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1233669792107292957403159931) ^ 2810181758786544322102870 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1233669792107292957403159931) ^ 23605030 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_1289745691748533546376030837 : Nat.Prime 1289745691748533546376030837 := by
  apply lucas_primality 1289745691748533546376030837 (2 : ZMod 1289745691748533546376030837)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (1303, 1), (18013, 1), (26367922070537711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (1303, 1), (18013, 1), (26367922070537711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1289745691748533546376030837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_521
      · exact prime_ninetySixCP_1303
      · exact prime_ninetySixCP_18013
      · exact prime_ninetySixCP_26367922070537711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1289745691748533546376030837) ^ 644872845874266773188015418 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1289745691748533546376030837) ^ 2475519561897377248322516 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1289745691748533546376030837) ^ 989827852454745622698412 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1289745691748533546376030837) ^ 71600826722285768410372 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1289745691748533546376030837) ^ 48913436876 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_2837440521846773802027267841 : Nat.Prime 2837440521846773802027267841 := by
  apply lucas_primality 2837440521846773802027267841 (7 : ZMod 2837440521846773802027267841)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 1), (246305600854754670314867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 1), (246305600854754670314867, 1)] : List FactorBlock).map factorBlockValue).prod) = 2837440521846773802027267841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_246305600854754670314867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2837440521846773802027267841) ^ 1418720260923386901013633920 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2837440521846773802027267841) ^ 945813507282257934009089280 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2837440521846773802027267841) ^ 567488104369354760405453568 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2837440521846773802027267841) ^ 11520 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_5404648613041473908623367317 : Nat.Prime 5404648613041473908623367317 := by
  apply lucas_primality 5404648613041473908623367317 (11 : ZMod 5404648613041473908623367317)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (41, 1), (16386113363, 1), (35283593052359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (41, 1), (16386113363, 1), (35283593052359, 1)] : List FactorBlock).map factorBlockValue).prod) = 5404648613041473908623367317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_19
      · exact prime_ninetySixCP_41
      · exact prime_ninetySixCP_16386113363
      · exact prime_ninetySixCP_35283593052359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5404648613041473908623367317) ^ 2702324306520736954311683658 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5404648613041473908623367317) ^ 1801549537680491302874455772 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5404648613041473908623367317) ^ 284455190160077574138071964 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5404648613041473908623367317) ^ 131820697879060339234716276 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5404648613041473908623367317) ^ 329831027853451932 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 5404648613041473908623367317) ^ 153177387717324 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_28374405218467738020272678417 : Nat.Prime 28374405218467738020272678417 := by
  apply lucas_primality 28374405218467738020272678417 (3 : ZMod 28374405218467738020272678417)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (617, 1), (14431, 1), (558112297, 1), (50980672697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (617, 1), (14431, 1), (558112297, 1), (50980672697, 1)] : List FactorBlock).map factorBlockValue).prod) = 28374405218467738020272678417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_7
      · exact prime_ninetySixCP_617
      · exact prime_ninetySixCP_14431
      · exact prime_ninetySixCP_558112297
      · exact prime_ninetySixCP_50980672697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28374405218467738020272678417) ^ 14187202609233869010136339208 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28374405218467738020272678417) ^ 4053486459781105431467525488 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28374405218467738020272678417) ^ 45987690791681909271106448 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28374405218467738020272678417) ^ 1966211989360940892541936 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28374405218467738020272678417) ^ 50839957067757885328 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 28374405218467738020272678417) ^ 556571808832515728 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_56748810436935476040545356807 : Nat.Prime 56748810436935476040545356807 := by
  apply lucas_primality 56748810436935476040545356807 (3 : ZMod 56748810436935476040545356807)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (41942184737, 1), (20500373706264643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (41942184737, 1), (20500373706264643, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935476040545356807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_11
      · exact prime_ninetySixCP_41942184737
      · exact prime_ninetySixCP_20500373706264643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56748810436935476040545356807) ^ 28374405218467738020272678403 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476040545356807) ^ 18916270145645158680181785602 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476040545356807) ^ 5158982766994134185504123346 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476040545356807) ^ 1353024664613466438 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476040545356807) ^ 2768184192642 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_56748810436935476040545356831 : Nat.Prime 56748810436935476040545356831 := by
  apply lucas_primality 56748810436935476040545356831 (11 : ZMod 56748810436935476040545356831)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (12888803, 1), (5060866997781252103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (12888803, 1), (5060866997781252103, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935476040545356831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_3
      · exact prime_ninetySixCP_5
      · exact prime_ninetySixCP_29
      · exact prime_ninetySixCP_12888803
      · exact prime_ninetySixCP_5060866997781252103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 56748810436935476040545356831) ^ 28374405218467738020272678415 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 56748810436935476040545356831) ^ 18916270145645158680181785610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 56748810436935476040545356831) ^ 11349762087387095208109071366 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 56748810436935476040545356831) ^ 1956855532308119863467081270 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 56748810436935476040545356831) ^ 4402954288069689329610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (11 : ZMod 56748810436935476040545356831) ^ 11213258610 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem prime_ninetySixCP_113497620873870952081090713647 : Nat.Prime 113497620873870952081090713647 := by
  apply lucas_primality 113497620873870952081090713647 (5 : ZMod 113497620873870952081090713647)
  · rw [← ninetySixCPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10847, 1), (5231751676678849086433609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10847, 1), (5231751676678849086433609, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySixCP_2
      · exact prime_ninetySixCP_10847
      · exact prime_ninetySixCP_5231751676678849086433609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 113497620873870952081090713647) ^ 56748810436935476040545356823 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 113497620873870952081090713647) ^ 10463503353357698172867218 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide
    · change (5 : ZMod 113497620873870952081090713647) ^ 21694 ≠ 1
      rw [← ninetySixCPFastPow_eq_pow]
      decide

private theorem phi_ninetySixCP_113497620873870952081090713600 : Nat.totient 113497620873870952081090713600 = 30266032233032253888290734080 := by
  rw [← show ((([(2, 11), (3, 2), (5, 2), (246305600854754670314867, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_246305600854754670314867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713601 : Nat.totient 113497620873870952081090713601 = 88435193034043492057786559040 := by
  rw [← show ((([(7, 1), (11, 1), (19603, 1), (23985900317, 1), (3134855077363, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_7, prime_ninetySixCP_11, prime_ninetySixCP_19603, prime_ninetySixCP_23985900317, prime_ninetySixCP_3134855077363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713602 : Nat.totient 113497620873870952081090713602 = 54791954558193757607952818688 := by
  rw [← show ((([(2, 1), (29, 2), (158160049, 1), (426642362611698889, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_29, prime_ninetySixCP_158160049, prime_ninetySixCP_426642362611698889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713603 : Nat.totient 113497620873870952081090713603 = 74750837427977965572497619264 := by
  rw [← show ((([(3, 1), (83, 1), (28579, 1), (15949254293337098290793, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_83, prime_ninetySixCP_28579, prime_ninetySixCP_15949254293337098290793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713604 : Nat.totient 113497620873870952081090713604 = 56690593896985868706242588640 := by
  rw [← show ((([(2, 2), (997, 1), (43711, 1), (651089761666040376403, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_997, prime_ninetySixCP_43711, prime_ninetySixCP_651089761666040376403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713605 : Nat.totient 113497620873870952081090713605 = 90798080239732991206590520000 := by
  rw [← show ((([(5, 1), (5516501, 1), (4114840942614564996221, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_5516501, prime_ninetySixCP_4114840942614564996221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713606 : Nat.totient 113497620873870952081090713606 = 35779266745264187306193973248 := by
  rw [← show ((([(2, 1), (3, 1), (23, 2), (89, 1), (20129, 1), (287020567, 1), (69543190447, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_23, prime_ninetySixCP_89, prime_ninetySixCP_20129, prime_ninetySixCP_287020567, prime_ninetySixCP_69543190447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713607 : Nat.totient 113497620873870952081090713607 = 113497236574086503642340859200 := by
  rw [← show ((([(309241, 1), (12559531, 1), (13859299, 1), (2108506783, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_309241, prime_ninetySixCP_12559531, prime_ninetySixCP_13859299, prime_ninetySixCP_2108506783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713608 : Nat.totient 113497620873870952081090713608 = 47915839942487097040631045952 := by
  rw [← show ((([(2, 3), (7, 1), (67, 1), (30249898953590339040802429, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_7, prime_ninetySixCP_67, prime_ninetySixCP_30249898953590339040802429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713609 : Nat.totient 113497620873870952081090713609 = 69841186987660340117011660800 := by
  rw [← show ((([(3, 2), (13, 2), (20681, 1), (556321, 1), (6485755241806129, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_13, prime_ninetySixCP_20681, prime_ninetySixCP_556321, prime_ninetySixCP_6485755241806129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713610 : Nat.totient 113497620873870952081090713610 = 42728512054450166224876772352 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (10578349, 1), (63113162929673314517, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_17, prime_ninetySixCP_10578349, prime_ninetySixCP_63113162929673314517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713611 : Nat.totient 113497620873870952081090713611 = 113497606715538951587719715952 := by
  rw [← show ((([(8016313, 1), (14158332000493362981347, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_8016313, prime_ninetySixCP_14158332000493362981347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713612 : Nat.totient 113497620873870952081090713612 = 34393218445807544610756180480 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (41942184737, 1), (20500373706264643, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_11, prime_ninetySixCP_41942184737, prime_ninetySixCP_20500373706264643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713613 : Nat.totient 113497620873870952081090713613 = 112161622747702877098706810880 := by
  rw [← show ((([(97, 1), (677, 1), (943105868581, 1), (1832592512117, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_97, prime_ninetySixCP_677, prime_ninetySixCP_943105868581, prime_ninetySixCP_1832592512117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713614 : Nat.totient 113497620873870952081090713614 = 56748810436935476040545356806 := by
  rw [← show ((([(2, 1), (56748810436935476040545356807, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_56748810436935476040545356807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713615 : Nat.totient 113497620873870952081090713615 = 51828813321964601555216263680 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (1039, 1), (8821, 1), (117940805426403893077, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_7, prime_ninetySixCP_1039, prime_ninetySixCP_8821, prime_ninetySixCP_117940805426403893077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713616 : Nat.totient 113497620873870952081090713616 = 56367945937358727879199413632 := by
  rw [← show ((([(2, 4), (149, 1), (47608062447093520168242749, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_149, prime_ninetySixCP_47608062447093520168242749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713617 : Nat.totient 113497620873870952081090713617 = 107524061880403785342077349360 := by
  rw [← show ((([(19, 1), (1018998619013, 1), (5862185563261711, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_19, prime_ninetySixCP_1018998619013, prime_ninetySixCP_5862185563261711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713618 : Nat.totient 113497620873870952081090713618 = 37640496858881358248075142720 := by
  rw [← show ((([(2, 1), (3, 5), (197, 1), (466560821, 1), (2540832266907899, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_197, prime_ninetySixCP_466560821, prime_ninetySixCP_2540832266907899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713619 : Nat.totient 113497620873870952081090713619 = 113211732660082864040584187496 := by
  rw [← show ((([(397, 1), (285888213788088040506525727, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_397, prime_ninetySixCP_285888213788088040506525727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713620 : Nat.totient 113497620873870952081090713620 = 45399048349536306009988409376 := by
  rw [← show ((([(2, 2), (5, 1), (3769223515567, 1), (1505583582468943, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_3769223515567, prime_ninetySixCP_1505583582468943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713621 : Nat.totient 113497620873870952081090713621 = 75611020635710137854152939376 := by
  rw [← show ((([(3, 1), (1423, 1), (85243, 1), (311890306758765743563, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_1423, prime_ninetySixCP_85243, prime_ninetySixCP_311890306758765743563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713622 : Nat.totient 113497620873870952081090713622 = 44464223323201304776085190144 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (103, 1), (4225073, 1), (1432992535954288759, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_7, prime_ninetySixCP_13, prime_ninetySixCP_103, prime_ninetySixCP_4225073, prime_ninetySixCP_1432992535954288759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713623 : Nat.totient 113497620873870952081090713623 = 97527599198733314169861120000 := by
  rw [← show ((([(11, 1), (31, 1), (71, 1), (157, 1), (337, 1), (3809837, 1), (23256164021221, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_11, prime_ninetySixCP_31, prime_ninetySixCP_71, prime_ninetySixCP_157, prime_ninetySixCP_337, prime_ninetySixCP_3809837, prime_ninetySixCP_23256164021221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713624 : Nat.totient 113497620873870952081090713624 = 37118352719987034953236895232 := by
  rw [← show ((([(2, 3), (3, 1), (53, 1), (127727, 1), (491983, 1), (1419929684623837, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_53, prime_ninetySixCP_127727, prime_ninetySixCP_491983, prime_ninetySixCP_1419929684623837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713625 : Nat.totient 113497620873870952081090713625 = 90772771634282142173497843200 := by
  rw [← show ((([(5, 3), (3593, 1), (1698947, 1), (124574557, 1), (1194016547, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_3593, prime_ninetySixCP_1698947, prime_ninetySixCP_124574557, prime_ninetySixCP_1194016547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713626 : Nat.totient 113497620873870952081090713626 = 56513338194458565351580438080 := by
  rw [← show ((([(2, 1), (241, 1), (235472242476910688964918493, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_241, prime_ninetySixCP_235472242476910688964918493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713627 : Nat.totient 113497620873870952081090713627 = 71084230923035711328436224000 := by
  rw [← show ((([(3, 2), (17, 1), (641, 1), (3779, 1), (1460821, 1), (209634811505261, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_17, prime_ninetySixCP_641, prime_ninetySixCP_3779, prime_ninetySixCP_1460821, prime_ninetySixCP_209634811505261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713628 : Nat.totient 113497620873870952081090713628 = 55541388938277274422661412960 := by
  rw [← show ((([(2, 2), (47, 1), (603710749329100808941971881, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_47, prime_ninetySixCP_603710749329100808941971881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713629 : Nat.totient 113497620873870952081090713629 = 92646715353237093148739654400 := by
  rw [← show ((([(7, 2), (23, 1), (233, 1), (16519, 1), (41131, 1), (636141750025871, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_7, prime_ninetySixCP_23, prime_ninetySixCP_233, prime_ninetySixCP_16519, prime_ninetySixCP_41131, prime_ninetySixCP_636141750025871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713630 : Nat.totient 113497620873870952081090713630 = 29448031361869219999418130816 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (37, 1), (102250108895379236109090733, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_37, prime_ninetySixCP_102250108895379236109090733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713631 : Nat.totient 113497620873870952081090713631 = 107768843617996291541900100480 := by
  rw [← show ((([(29, 1), (61, 1), (11159, 1), (12043, 1), (477418189122235027, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_29, prime_ninetySixCP_61, prime_ninetySixCP_11159, prime_ninetySixCP_12043, prime_ninetySixCP_477418189122235027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713632 : Nat.totient 113497620873870952081090713632 = 55936925597118536983272978432 := by
  rw [← show ((([(2, 5), (79, 1), (599, 1), (16196249, 1), (35805727, 1), (129245647, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_79, prime_ninetySixCP_599, prime_ninetySixCP_16196249, prime_ninetySixCP_35805727, prime_ninetySixCP_129245647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713633 : Nat.totient 113497620873870952081090713633 = 73900119334032713195857152000 := by
  rw [← show ((([(3, 1), (43, 1), (27361, 1), (37511, 1), (116027, 1), (7388348564981, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_43, prime_ninetySixCP_27361, prime_ninetySixCP_37511, prime_ninetySixCP_116027, prime_ninetySixCP_7388348564981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713634 : Nat.totient 113497620873870952081090713634 = 51585274678614384076275858000 := by
  rw [← show ((([(2, 1), (11, 1), (12203, 1), (158551, 1), (2666419522326260399, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_11, prime_ninetySixCP_12203, prime_ninetySixCP_158551, prime_ninetySixCP_2666419522326260399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713635 : Nat.totient 113497620873870952081090713635 = 83813627722238537129048302848 := by
  rw [← show ((([(5, 1), (13, 1), (24173636860507, 1), (72232293977497, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_13, prime_ninetySixCP_24173636860507, prime_ninetySixCP_72232293977497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713636 : Nat.totient 113497620873870952081090713636 = 29971863936987978842889776640 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (19, 1), (41, 1), (16386113363, 1), (35283593052359, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_7, prime_ninetySixCP_19, prime_ninetySixCP_41, prime_ninetySixCP_16386113363, prime_ninetySixCP_35283593052359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713637 : Nat.totient 113497620873870952081090713637 = 113384221725646222509095561520 := by
  rw [← show ((([(1171, 1), (6883, 1), (14081602908820262260909, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_1171, prime_ninetySixCP_6883, prime_ninetySixCP_14081602908820262260909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713638 : Nat.totient 113497620873870952081090713638 = 56748475965232452261754729696 := by
  rw [← show ((([(2, 1), (169667, 1), (334471703023778790457457, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_169667, prime_ninetySixCP_334471703023778790457457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713639 : Nat.totient 113497620873870952081090713639 = 75664616971477907064241214400 := by
  rw [← show ((([(3, 1), (163211, 1), (9143445161, 1), (25351648984303, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_163211, prime_ninetySixCP_9143445161, prime_ninetySixCP_25351648984303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713640 : Nat.totient 113497620873870952081090713640 = 45399048349548380832436285440 := by
  rw [← show ((([(2, 3), (5, 1), (2837440521846773802027267841, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_2837440521846773802027267841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713641 : Nat.totient 113497620873870952081090713641 = 112994069403750909732723456000 := by
  rw [← show ((([(281, 1), (1151, 1), (90547, 1), (804197, 1), (4819129534129, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_281, prime_ninetySixCP_1151, prime_ninetySixCP_90547, prime_ninetySixCP_804197, prime_ninetySixCP_4819129534129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713642 : Nat.totient 113497620873870952081090713642 = 37832540291252861617793597472 := by
  rw [← show ((([(2, 1), (3, 1), (1010114293753, 1), (18726861170693119, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_1010114293753, prime_ninetySixCP_18726861170693119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713643 : Nat.totient 113497620873870952081090713643 = 96391164254386061215902565152 := by
  rw [← show ((([(7, 1), (109, 1), (428591578159, 1), (347071207810879, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_7, prime_ninetySixCP_109, prime_ninetySixCP_428591578159, prime_ninetySixCP_347071207810879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713644 : Nat.totient 113497620873870952081090713644 = 53242092365030921251908000768 := by
  rw [← show ((([(2, 2), (17, 1), (317, 1), (820213, 1), (6419362999541336123, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_17, prime_ninetySixCP_317, prime_ninetySixCP_820213, prime_ninetySixCP_6419362999541336123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713645 : Nat.totient 113497620873870952081090713645 = 55029149514604097978710641120 := by
  rw [← show ((([(3, 3), (5, 1), (11, 2), (6948124938712638633675587, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_11, prime_ninetySixCP_6948124938712638633675587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713646 : Nat.totient 113497620873870952081090713646 = 56743578685258797191458912368 := by
  rw [← show ((([(2, 1), (10847, 1), (5231751676678849086433609, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_10847, prime_ninetySixCP_5231751676678849086433609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713647 : Nat.totient 113497620873870952081090713647 = 113497620873870952081090713646 := by
  rw [← show ((([(113497620873870952081090713647, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_113497620873870952081090713647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713648 : Nat.totient 113497620873870952081090713648 = 34916697861587658365837607936 := by
  rw [← show ((([(2, 4), (3, 1), (13, 1), (6203, 1), (2040653, 1), (14369154854654203, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_13, prime_ninetySixCP_6203, prime_ninetySixCP_2040653, prime_ninetySixCP_14369154854654203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713649 : Nat.totient 113497620873870952081090713649 = 111568401529757463224485149456 := by
  rw [← show ((([(59, 1), (20173, 1), (95359564238717258494607, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_59, prime_ninetySixCP_20173, prime_ninetySixCP_95359564238717258494607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713650 : Nat.totient 113497620873870952081090713650 = 38806721156170030688093894400 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (383, 1), (8629, 1), (59771, 1), (1641606068218687, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_7, prime_ninetySixCP_383, prime_ninetySixCP_8629, prime_ninetySixCP_59771, prime_ninetySixCP_1641606068218687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713651 : Nat.totient 113497620873870952081090713651 = 75665080569254918903030292552 := by
  rw [← show ((([(3, 1), (5678125039, 1), (6662857903170299903, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_5678125039, prime_ninetySixCP_6662857903170299903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713652 : Nat.totient 113497620873870952081090713652 = 54281470852720890125739036920 := by
  rw [← show ((([(2, 2), (23, 1), (1233669792107292957403159931, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_23, prime_ninetySixCP_1233669792107292957403159931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713653 : Nat.totient 113497620873870952081090713653 = 112615367965050329514635900400 := by
  rw [← show ((([(131, 1), (7459, 1), (148411, 1), (782652116068132087, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_131, prime_ninetySixCP_7459, prime_ninetySixCP_148411, prime_ninetySixCP_782652116068132087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713654 : Nat.totient 113497620873870952081090713654 = 36473958296294848172977536000 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (313, 1), (1721, 1), (377595970568877627181, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_31, prime_ninetySixCP_313, prime_ninetySixCP_1721, prime_ninetySixCP_377595970568877627181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713655 : Nat.totient 113497620873870952081090713655 = 85964355530191050533906227200 := by
  rw [← show ((([(5, 1), (19, 1), (1601, 1), (73757, 1), (10117391994920452157, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_19, prime_ninetySixCP_1601, prime_ninetySixCP_73757, prime_ninetySixCP_10117391994920452157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713656 : Nat.totient 113497620873870952081090713656 = 51589827669941341855041233440 := by
  rw [← show ((([(2, 3), (11, 1), (1289745691748533546376030837, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_11, prime_ninetySixCP_1289745691748533546376030837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713657 : Nat.totient 113497620873870952081090713657 = 64855783356497686903480407792 := by
  rw [← show ((([(3, 1), (7, 1), (5404648613041473908623367317, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_7, prime_ninetySixCP_5404648613041473908623367317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713658 : Nat.totient 113497620873870952081090713658 = 56406054876270694225245014400 := by
  rw [← show ((([(2, 1), (181, 1), (1931, 1), (197281267, 1), (823019386416217, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_181, prime_ninetySixCP_1931, prime_ninetySixCP_197281267, prime_ninetySixCP_823019386416217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713659 : Nat.totient 113497620873870952081090713659 = 113475923756517889387135233240 := by
  rw [← show ((([(5231, 1), (21697117353062693955475189, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5231, prime_ninetySixCP_21697117353062693955475189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713660 : Nat.totient 113497620873870952081090713660 = 29222373681866174949333288192 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (29, 1), (12888803, 1), (5060866997781252103, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_29, prime_ninetySixCP_12888803, prime_ninetySixCP_5060866997781252103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713661 : Nat.totient 113497620873870952081090713661 = 98039340174166176930845122560 := by
  rw [← show ((([(13, 1), (17, 1), (179, 1), (6971, 1), (411572520599612710049, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_13, prime_ninetySixCP_17, prime_ninetySixCP_179, prime_ninetySixCP_6971, prime_ninetySixCP_411572520599612710049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713662 : Nat.totient 113497620873870952081090713662 = 56748810436935476040545356830 := by
  rw [← show ((([(2, 1), (56748810436935476040545356831, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_56748810436935476040545356831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713663 : Nat.totient 113497620873870952081090713663 = 75476389608559236629154254400 := by
  rw [← show ((([(3, 2), (401, 1), (31448495670233015262147607, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_401, prime_ninetySixCP_31448495670233015262147607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713664 : Nat.totient 113497620873870952081090713664 = 48559636201896584579293839360 := by
  rw [← show ((([(2, 6), (7, 1), (617, 1), (14431, 1), (558112297, 1), (50980672697, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_7, prime_ninetySixCP_617, prime_ninetySixCP_14431, prime_ninetySixCP_558112297, prime_ninetySixCP_50980672697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713665 : Nat.totient 113497620873870952081090713665 = 90002990519805887148600285120 := by
  rw [← show ((([(5, 1), (167, 1), (359, 1), (378621990138511674415261, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_167, prime_ninetySixCP_359, prime_ninetySixCP_378621990138511674415261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713666 : Nat.totient 113497620873870952081090713666 = 37832540290551815894711205984 := by
  rw [← show ((([(2, 1), (3, 1), (51228802243, 1), (369250681597380377, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_51228802243, prime_ninetySixCP_369250681597380377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713667 : Nat.totient 113497620873870952081090713667 = 100391016006372340907107251840 := by
  rw [← show ((([(11, 1), (37, 2), (7536863063541467035068113, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_11, prime_ninetySixCP_37, prime_ninetySixCP_7536863063541467035068113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713668 : Nat.totient 113497620873870952081090713668 = 56748810436935476040545356832 := by
  rw [← show ((([(2, 2), (28374405218467738020272678417, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_28374405218467738020272678417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713669 : Nat.totient 113497620873870952081090713669 = 75418597188100568390040589680 := by
  rw [← show ((([(3, 1), (307, 1), (4350919, 1), (28323448509335454731, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_307, prime_ninetySixCP_4350919, prime_ninetySixCP_28323448509335454731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713670 : Nat.totient 113497620873870952081090713670 = 45316051917358043610009381888 := by
  rw [← show ((([(2, 1), (5, 1), (547, 1), (426964954657, 1), (48596747331373, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_547, prime_ninetySixCP_426964954657, prime_ninetySixCP_48596747331373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713671 : Nat.totient 113497620873870952081090713671 = 97252504360272084174395466240 := by
  rw [← show ((([(7, 1), (3121, 1), (5195112412407696804187793, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_7, prime_ninetySixCP_3121, prime_ninetySixCP_5195112412407696804187793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713672 : Nat.totient 113497620873870952081090713672 = 37314262630199808903409145856 := by
  rw [← show ((([(2, 3), (3, 3), (73, 1), (1575473, 1), (4568768806019049923, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_73, prime_ninetySixCP_1575473, prime_ninetySixCP_4568768806019049923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713673 : Nat.totient 113497620873870952081090713673 = 113414162244527518089570247680 := by
  rw [← show ((([(1361, 1), (1793479, 1), (44001809, 1), (1056724570063, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_1361, prime_ninetySixCP_1793479, prime_ninetySixCP_44001809, prime_ninetySixCP_1056724570063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713674 : Nat.totient 113497620873870952081090713674 = 49626490047447017894980545792 := by
  rw [← show ((([(2, 1), (13, 1), (19, 1), (968329457, 1), (237266632048194803, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_13, prime_ninetySixCP_19, prime_ninetySixCP_968329457, prime_ninetySixCP_237266632048194803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713675 : Nat.totient 113497620873870952081090713675 = 55226079917660501459140608000 := by
  rw [← show ((([(3, 1), (5, 2), (23, 1), (47, 1), (67, 1), (127, 1), (353, 1), (183886177, 1), (2534530301, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_23, prime_ninetySixCP_47, prime_ninetySixCP_67, prime_ninetySixCP_127, prime_ninetySixCP_353, prime_ninetySixCP_183886177, prime_ninetySixCP_2534530301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713676 : Nat.totient 113497620873870952081090713676 = 55422039178483587025315292736 := by
  rw [← show ((([(2, 2), (43, 1), (7883, 1), (4705518583, 1), (17789317715597, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_43, prime_ninetySixCP_7883, prime_ninetySixCP_4705518583, prime_ninetySixCP_17789317715597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713677 : Nat.totient 113497620873870952081090713677 = 107214952978269817293144064000 := by
  rw [← show ((([(41, 1), (53, 1), (101, 1), (347, 1), (2753, 1), (175433, 1), (3085735391183, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_41, prime_ninetySixCP_53, prime_ninetySixCP_101, prime_ninetySixCP_347, prime_ninetySixCP_2753, prime_ninetySixCP_175433, prime_ninetySixCP_3085735391183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713678 : Nat.totient 113497620873870952081090713678 = 27745771454201579053273098240 := by
  rw [← show ((([(2, 1), (3, 1), (7, 3), (11, 1), (17, 1), (1523069, 1), (193633369236474197, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_7, prime_ninetySixCP_11, prime_ninetySixCP_17, prime_ninetySixCP_1523069, prime_ninetySixCP_193633369236474197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713679 : Nat.totient 113497620873870952081090713679 = 112908748526597818336496693760 := by
  rw [← show ((([(193, 1), (140827, 1), (9514646611, 1), (438885121999, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_193, prime_ninetySixCP_140827, prime_ninetySixCP_9514646611, prime_ninetySixCP_438885121999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713680 : Nat.totient 113497620873870952081090713680 = 45130893010001548313728647168 := by
  rw [← show ((([(2, 4), (5, 1), (173, 1), (7873, 1), (14942647117, 1), (69708040697, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_173, prime_ninetySixCP_7873, prime_ninetySixCP_14942647117, prime_ninetySixCP_69708040697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713681 : Nat.totient 113497620873870952081090713681 = 75665077851479988703759140096 := by
  rw [← show ((([(3, 2), (27704977, 1), (455183441002800295417, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_27704977, prime_ninetySixCP_455183441002800295417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713682 : Nat.totient 113497620873870952081090713682 = 56731110801265639940838094080 := by
  rw [← show ((([(2, 1), (3691, 1), (24413, 1), (69333713, 1), (9083372145479, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3691, prime_ninetySixCP_24413, prime_ninetySixCP_69333713, prime_ninetySixCP_9083372145479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713683 : Nat.totient 113497620873870952081090713683 = 113497620873681464770222330848 := by
  rw [← show ((([(598974037489, 1), (189486711894345347, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_598974037489, prime_ninetySixCP_189486711894345347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713684 : Nat.totient 113497620873870952081090713684 = 37478964749281111049970576096 := by
  rw [← show ((([(2, 2), (3, 1), (107, 1), (93908719, 1), (941273469264486779, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_107, prime_ninetySixCP_93908719, prime_ninetySixCP_941273469264486779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713685 : Nat.totient 113497620873870952081090713685 = 75175657631601458800806144000 := by
  rw [← show ((([(5, 1), (7, 1), (31, 1), (601, 1), (4877, 1), (35688623051492504293, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_7, prime_ninetySixCP_31, prime_ninetySixCP_601, prime_ninetySixCP_4877, prime_ninetySixCP_35688623051492504293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713686 : Nat.totient 113497620873870952081090713686 = 56063176046764313274116549280 := by
  rw [← show ((([(2, 1), (83, 1), (29303, 1), (113464717, 1), (205639126574971, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_83, prime_ninetySixCP_29303, prime_ninetySixCP_113464717, prime_ninetySixCP_205639126574971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713687 : Nat.totient 113497620873870952081090713687 = 69362883404514960794120764800 := by
  rw [← show ((([(3, 1), (13, 1), (211, 1), (461, 1), (29918427969511283986423, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_13, prime_ninetySixCP_211, prime_ninetySixCP_461, prime_ninetySixCP_29918427969511283986423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713688 : Nat.totient 113497620873870952081090713688 = 56552754473401378004590023936 := by
  rw [← show ((([(2, 3), (523, 1), (647, 1), (8491487, 1), (4937499360646313, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_523, prime_ninetySixCP_647, prime_ninetySixCP_8491487, prime_ninetySixCP_4937499360646313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713689 : Nat.totient 113497620873870952081090713689 = 99614349687277032095782103040 := by
  rw [← show ((([(11, 1), (29, 1), (13487, 1), (50538607897, 1), (521984302129, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_11, prime_ninetySixCP_29, prime_ninetySixCP_13487, prime_ninetySixCP_50538607897, prime_ninetySixCP_521984302129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713690 : Nat.totient 113497620873870952081090713690 = 30225775683530516230045449216 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (757, 1), (109943, 1), (400670147, 1), (37817585753, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_5, prime_ninetySixCP_757, prime_ninetySixCP_109943, prime_ninetySixCP_400670147, prime_ninetySixCP_37817585753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713691 : Nat.totient 113497620873870952081090713691 = 112493217149323421531700530272 := by
  rw [← show ((([(113, 1), (1004403724547530549390183307, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_113, prime_ninetySixCP_1004403724547530549390183307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713692 : Nat.totient 113497620873870952081090713692 = 47844430101014497593286104000 := by
  rw [← show ((([(2, 2), (7, 1), (61, 1), (196129699, 1), (338809461494812151, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_7, prime_ninetySixCP_61, prime_ninetySixCP_196129699, prime_ninetySixCP_338809461494812151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713693 : Nat.totient 113497620873870952081090713693 = 71566650515328735804200251200 := by
  rw [← show ((([(3, 1), (19, 1), (883, 1), (2053, 1), (1098404363153633149051, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_19, prime_ninetySixCP_883, prime_ninetySixCP_2053, prime_ninetySixCP_1098404363153633149051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713694 : Nat.totient 113497620873870952081090713694 = 55779796667803747805570304000 := by
  rw [← show ((([(2, 1), (71, 1), (331, 1), (79393, 1), (161914019, 1), (187846779641, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_71, prime_ninetySixCP_331, prime_ninetySixCP_79393, prime_ninetySixCP_161914019, prime_ninetySixCP_187846779641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713695 : Nat.totient 113497620873870952081090713695 = 84496840814429803482228228096 := by
  rw [← show ((([(5, 1), (17, 1), (89, 1), (1544207075809, 1), (9715659535867, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_5, prime_ninetySixCP_17, prime_ninetySixCP_89, prime_ninetySixCP_1544207075809, prime_ninetySixCP_9715659535867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713696 : Nat.totient 113497620873870952081090713696 = 37802914182996433008476009984 := by
  rw [← show ((([(2, 5), (3, 1), (1277, 1), (925815884183885996485013, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_3, prime_ninetySixCP_1277, prime_ninetySixCP_925815884183885996485013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713697 : Nat.totient 113497620873870952081090713697 = 113497620860280226500171622080 := by
  rw [← show ((([(8351108281, 1), (13590725572567983337, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_8351108281, prime_ninetySixCP_13590725572567983337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713698 : Nat.totient 113497620873870952081090713698 = 54281470848257106330189888960 := by
  rw [← show ((([(2, 1), (23, 1), (12160417393, 1), (202899251273634791, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_23, prime_ninetySixCP_12160417393, prime_ninetySixCP_202899251273634791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713699 : Nat.totient 113497620873870952081090713699 = 64851938124431716337222762496 := by
  rw [← show ((([(3, 4), (7, 1), (18049, 1), (257437, 1), (43080386241022969, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_3, prime_ninetySixCP_7, prime_ninetySixCP_18049, prime_ninetySixCP_257437, prime_ninetySixCP_43080386241022969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713700 : Nat.totient 113497620873870952081090713700 = 38094099113107794818223360000 := by
  rw [← show ((([(2, 2), (5, 2), (11, 1), (13, 1), (13799, 1), (156421, 1), (3677122073530021, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_2, prime_ninetySixCP_5, prime_ninetySixCP_11, prime_ninetySixCP_13, prime_ninetySixCP_13799, prime_ninetySixCP_156421, prime_ninetySixCP_3677122073530021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySixCP_113497620873870952081090713701 : Nat.totient 113497620873870952081090713701 = 113001891283531737754254615888 := by
  rw [← show ((([(367, 1), (607, 1), (509485704356849256768629, 1)] : List FactorBlock).map factorBlockValue).prod) = 113497620873870952081090713701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySixCP_367, prime_ninetySixCP_607, prime_ninetySixCP_509485704356849256768629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetySixCP : certifiedKill 1 113497620873870952081090713599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetySixCP_113497620873870952081090713600, phi_ninetySixCP_113497620873870952081090713601, phi_ninetySixCP_113497620873870952081090713602,
    phi_ninetySixCP_113497620873870952081090713603, phi_ninetySixCP_113497620873870952081090713604, phi_ninetySixCP_113497620873870952081090713605,
    phi_ninetySixCP_113497620873870952081090713606, phi_ninetySixCP_113497620873870952081090713607, phi_ninetySixCP_113497620873870952081090713608,
    phi_ninetySixCP_113497620873870952081090713609, phi_ninetySixCP_113497620873870952081090713610, phi_ninetySixCP_113497620873870952081090713611,
    phi_ninetySixCP_113497620873870952081090713612, phi_ninetySixCP_113497620873870952081090713613, phi_ninetySixCP_113497620873870952081090713614,
    phi_ninetySixCP_113497620873870952081090713615, phi_ninetySixCP_113497620873870952081090713616, phi_ninetySixCP_113497620873870952081090713617,
    phi_ninetySixCP_113497620873870952081090713618, phi_ninetySixCP_113497620873870952081090713619, phi_ninetySixCP_113497620873870952081090713620,
    phi_ninetySixCP_113497620873870952081090713621, phi_ninetySixCP_113497620873870952081090713622, phi_ninetySixCP_113497620873870952081090713623,
    phi_ninetySixCP_113497620873870952081090713624, phi_ninetySixCP_113497620873870952081090713625, phi_ninetySixCP_113497620873870952081090713626,
    phi_ninetySixCP_113497620873870952081090713627, phi_ninetySixCP_113497620873870952081090713628, phi_ninetySixCP_113497620873870952081090713629,
    phi_ninetySixCP_113497620873870952081090713630, phi_ninetySixCP_113497620873870952081090713631, phi_ninetySixCP_113497620873870952081090713632,
    phi_ninetySixCP_113497620873870952081090713633, phi_ninetySixCP_113497620873870952081090713634, phi_ninetySixCP_113497620873870952081090713635,
    phi_ninetySixCP_113497620873870952081090713636, phi_ninetySixCP_113497620873870952081090713637, phi_ninetySixCP_113497620873870952081090713638,
    phi_ninetySixCP_113497620873870952081090713639, phi_ninetySixCP_113497620873870952081090713640, phi_ninetySixCP_113497620873870952081090713641,
    phi_ninetySixCP_113497620873870952081090713642, phi_ninetySixCP_113497620873870952081090713643, phi_ninetySixCP_113497620873870952081090713644,
    phi_ninetySixCP_113497620873870952081090713645, phi_ninetySixCP_113497620873870952081090713646, phi_ninetySixCP_113497620873870952081090713647,
    phi_ninetySixCP_113497620873870952081090713648, phi_ninetySixCP_113497620873870952081090713649, phi_ninetySixCP_113497620873870952081090713650,
    phi_ninetySixCP_113497620873870952081090713651, phi_ninetySixCP_113497620873870952081090713652, phi_ninetySixCP_113497620873870952081090713653,
    phi_ninetySixCP_113497620873870952081090713654, phi_ninetySixCP_113497620873870952081090713655, phi_ninetySixCP_113497620873870952081090713656,
    phi_ninetySixCP_113497620873870952081090713657, phi_ninetySixCP_113497620873870952081090713658, phi_ninetySixCP_113497620873870952081090713659,
    phi_ninetySixCP_113497620873870952081090713660, phi_ninetySixCP_113497620873870952081090713661, phi_ninetySixCP_113497620873870952081090713662,
    phi_ninetySixCP_113497620873870952081090713663, phi_ninetySixCP_113497620873870952081090713664, phi_ninetySixCP_113497620873870952081090713665,
    phi_ninetySixCP_113497620873870952081090713666, phi_ninetySixCP_113497620873870952081090713667, phi_ninetySixCP_113497620873870952081090713668,
    phi_ninetySixCP_113497620873870952081090713669, phi_ninetySixCP_113497620873870952081090713670, phi_ninetySixCP_113497620873870952081090713671,
    phi_ninetySixCP_113497620873870952081090713672, phi_ninetySixCP_113497620873870952081090713673, phi_ninetySixCP_113497620873870952081090713674,
    phi_ninetySixCP_113497620873870952081090713675, phi_ninetySixCP_113497620873870952081090713676, phi_ninetySixCP_113497620873870952081090713677,
    phi_ninetySixCP_113497620873870952081090713678, phi_ninetySixCP_113497620873870952081090713679, phi_ninetySixCP_113497620873870952081090713680,
    phi_ninetySixCP_113497620873870952081090713681, phi_ninetySixCP_113497620873870952081090713682, phi_ninetySixCP_113497620873870952081090713683,
    phi_ninetySixCP_113497620873870952081090713684, phi_ninetySixCP_113497620873870952081090713685, phi_ninetySixCP_113497620873870952081090713686,
    phi_ninetySixCP_113497620873870952081090713687, phi_ninetySixCP_113497620873870952081090713688, phi_ninetySixCP_113497620873870952081090713689,
    phi_ninetySixCP_113497620873870952081090713690, phi_ninetySixCP_113497620873870952081090713691, phi_ninetySixCP_113497620873870952081090713692,
    phi_ninetySixCP_113497620873870952081090713693, phi_ninetySixCP_113497620873870952081090713694, phi_ninetySixCP_113497620873870952081090713695,
    phi_ninetySixCP_113497620873870952081090713696, phi_ninetySixCP_113497620873870952081090713697, phi_ninetySixCP_113497620873870952081090713698,
    phi_ninetySixCP_113497620873870952081090713699, phi_ninetySixCP_113497620873870952081090713700, phi_ninetySixCP_113497620873870952081090713701
    ]

end TotientTailPeriodKiller
end Erdos249257
