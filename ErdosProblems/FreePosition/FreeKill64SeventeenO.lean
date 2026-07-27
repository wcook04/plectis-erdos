import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open private
  prime_t64_2
  prime_t64_3
  prime_t64_5
  prime_t64_7
  prime_t64_11
  prime_t64_13
  prime_t64_17
  prime_t64_19
  prime_t64_23
  prime_t64_29
  prime_t64_31
  prime_t64_37
  prime_t64_41
  prime_t64_43
  prime_t64_47
  prime_t64_53
  prime_t64_59
  prime_t64_61
  prime_t64_67
  prime_t64_71
  prime_t64_73
  prime_t64_79
  prime_t64_83
  prime_t64_89
  prime_t64_97
  prime_t64_101
  prime_t64_103
  prime_t64_107
  prime_t64_109
  prime_t64_113
  prime_t64_137
  prime_t64_139
  prime_t64_149
  prime_t64_157
  prime_t64_163
  prime_t64_167
  prime_t64_179
  prime_t64_191
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_227
  prime_t64_229
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_283
  prime_t64_307
  prime_t64_311
  prime_t64_317
  prime_t64_349
  prime_t64_431
  prime_t64_439
  prime_t64_461
  prime_t64_491
  prime_t64_499
  prime_t64_521
  prime_t64_761
  prime_t64_883
  prime_t64_997
  prime_t64_1051
  prime_t64_1061
  prime_t64_1093
  prime_t64_1153
  prime_t64_1373
  prime_t64_5009
  prime_t64_8543
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private def seventeenOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventeenOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    seventeenOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventeenOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventeenOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventeenOFastPow a n * seventeenOFastPow a n * a
        else seventeenOFastPow a n * seventeenOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventeenO_127 : Nat.Prime 127 := by norm_num

private theorem prime_seventeenO_151 : Nat.Prime 151 := by norm_num

private theorem prime_seventeenO_173 : Nat.Prime 173 := by norm_num

private theorem prime_seventeenO_181 : Nat.Prime 181 := by norm_num

private theorem prime_seventeenO_199 : Nat.Prime 199 := by norm_num

private theorem prime_seventeenO_211 : Nat.Prime 211 := by norm_num

private theorem prime_seventeenO_241 : Nat.Prime 241 := by norm_num

private theorem prime_seventeenO_257 : Nat.Prime 257 := by norm_num

private theorem prime_seventeenO_271 : Nat.Prime 271 := by norm_num

private theorem prime_seventeenO_277 : Nat.Prime 277 := by norm_num

private theorem prime_seventeenO_293 : Nat.Prime 293 := by norm_num

private theorem prime_seventeenO_313 : Nat.Prime 313 := by norm_num

private theorem prime_seventeenO_331 : Nat.Prime 331 := by norm_num

private theorem prime_seventeenO_337 : Nat.Prime 337 := by norm_num

private theorem prime_seventeenO_347 : Nat.Prime 347 := by norm_num

private theorem prime_seventeenO_353 : Nat.Prime 353 := by norm_num

private theorem prime_seventeenO_359 : Nat.Prime 359 := by norm_num

private theorem prime_seventeenO_367 : Nat.Prime 367 := by norm_num

private theorem prime_seventeenO_397 : Nat.Prime 397 := by norm_num

private theorem prime_seventeenO_419 : Nat.Prime 419 := by norm_num

private theorem prime_seventeenO_449 : Nat.Prime 449 := by norm_num

private theorem prime_seventeenO_487 : Nat.Prime 487 := by norm_num

private theorem prime_seventeenO_509 : Nat.Prime 509 := by norm_num

private theorem prime_seventeenO_523 : Nat.Prime 523 := by norm_num

private theorem prime_seventeenO_541 : Nat.Prime 541 := by norm_num

private theorem prime_seventeenO_557 : Nat.Prime 557 := by norm_num

private theorem prime_seventeenO_569 : Nat.Prime 569 := by norm_num

private theorem prime_seventeenO_571 : Nat.Prime 571 := by norm_num

private theorem prime_seventeenO_577 : Nat.Prime 577 := by norm_num

private theorem prime_seventeenO_587 : Nat.Prime 587 := by norm_num

private theorem prime_seventeenO_593 : Nat.Prime 593 := by norm_num

private theorem prime_seventeenO_599 : Nat.Prime 599 := by norm_num

private theorem prime_seventeenO_631 : Nat.Prime 631 := by norm_num

private theorem prime_seventeenO_677 : Nat.Prime 677 := by norm_num

private theorem prime_seventeenO_709 : Nat.Prime 709 := by norm_num

private theorem prime_seventeenO_727 : Nat.Prime 727 := by norm_num

private theorem prime_seventeenO_739 : Nat.Prime 739 := by norm_num

private theorem prime_seventeenO_743 : Nat.Prime 743 := by norm_num

private theorem prime_seventeenO_757 : Nat.Prime 757 := by norm_num

private theorem prime_seventeenO_773 : Nat.Prime 773 := by norm_num

private theorem prime_seventeenO_853 : Nat.Prime 853 := by norm_num

private theorem prime_seventeenO_887 : Nat.Prime 887 := by norm_num

private theorem prime_seventeenO_919 : Nat.Prime 919 := by norm_num

private theorem prime_seventeenO_937 : Nat.Prime 937 := by norm_num

private theorem prime_seventeenO_941 : Nat.Prime 941 := by norm_num

private theorem prime_seventeenO_947 : Nat.Prime 947 := by norm_num

private theorem prime_seventeenO_971 : Nat.Prime 971 := by norm_num

private theorem prime_seventeenO_977 : Nat.Prime 977 := by norm_num

private theorem prime_seventeenO_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_seventeenO_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_seventeenO_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_seventeenO_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_seventeenO_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_seventeenO_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_seventeenO_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_seventeenO_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_seventeenO_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_seventeenO_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_seventeenO_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_seventeenO_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_seventeenO_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_seventeenO_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_seventeenO_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_seventeenO_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_seventeenO_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_seventeenO_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_seventeenO_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_seventeenO_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_seventeenO_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_seventeenO_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_seventeenO_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_seventeenO_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_seventeenO_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_seventeenO_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_seventeenO_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_seventeenO_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_seventeenO_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_seventeenO_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_seventeenO_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_seventeenO_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_seventeenO_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_seventeenO_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_seventeenO_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_seventeenO_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_seventeenO_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_seventeenO_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_seventeenO_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_seventeenO_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_seventeenO_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_seventeenO_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_seventeenO_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_seventeenO_3671 : Nat.Prime 3671 := by norm_num

private theorem prime_seventeenO_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_seventeenO_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_seventeenO_3853 : Nat.Prime 3853 := by norm_num

private theorem prime_seventeenO_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_seventeenO_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_seventeenO_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_seventeenO_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_seventeenO_4591 : Nat.Prime 4591 := by norm_num

private theorem prime_seventeenO_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_seventeenO_4861 : Nat.Prime 4861 := by norm_num

private theorem prime_seventeenO_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_seventeenO_5261 : Nat.Prime 5261 := by norm_num

private theorem prime_seventeenO_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_seventeenO_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_seventeenO_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_seventeenO_5659 : Nat.Prime 5659 := by norm_num

private theorem prime_seventeenO_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_seventeenO_5839 : Nat.Prime 5839 := by norm_num

private theorem prime_seventeenO_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_seventeenO_6287 : Nat.Prime 6287 := by norm_num

private theorem prime_seventeenO_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_seventeenO_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_seventeenO_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_seventeenO_6737 : Nat.Prime 6737 := by norm_num

private theorem prime_seventeenO_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_seventeenO_6971 : Nat.Prime 6971 := by norm_num

private theorem prime_seventeenO_6991 : Nat.Prime 6991 := by norm_num

private theorem prime_seventeenO_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_seventeenO_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_seventeenO_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_seventeenO_7529 : Nat.Prime 7529 := by norm_num

private theorem prime_seventeenO_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_seventeenO_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_seventeenO_9689 : Nat.Prime 9689 := by norm_num

private theorem prime_seventeenO_9929 : Nat.Prime 9929 := by norm_num

private theorem prime_seventeenO_9973 : Nat.Prime 9973 := by norm_num

private theorem prime_seventeenO_10151 : Nat.Prime 10151 := by norm_num

private theorem prime_seventeenO_10181 : Nat.Prime 10181 := by norm_num

private theorem prime_seventeenO_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_seventeenO_10597 : Nat.Prime 10597 := by norm_num

private theorem prime_seventeenO_10837 : Nat.Prime 10837 := by norm_num

private theorem prime_seventeenO_11149 : Nat.Prime 11149 := by norm_num

private theorem prime_seventeenO_11197 : Nat.Prime 11197 := by norm_num

private theorem prime_seventeenO_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_seventeenO_11833 : Nat.Prime 11833 := by norm_num

private theorem prime_seventeenO_12263 : Nat.Prime 12263 := by norm_num

private theorem prime_seventeenO_12269 : Nat.Prime 12269 := by norm_num

private theorem prime_seventeenO_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_seventeenO_12373 : Nat.Prime 12373 := by norm_num

private theorem prime_seventeenO_12703 : Nat.Prime 12703 := by norm_num

private theorem prime_seventeenO_12973 : Nat.Prime 12973 := by norm_num

private theorem prime_seventeenO_13001 : Nat.Prime 13001 := by norm_num

private theorem prime_seventeenO_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_seventeenO_14897 : Nat.Prime 14897 := by norm_num

private theorem prime_seventeenO_15727 : Nat.Prime 15727 := by norm_num

private theorem prime_seventeenO_15913 : Nat.Prime 15913 := by norm_num

private theorem prime_seventeenO_16111 : Nat.Prime 16111 := by norm_num

private theorem prime_seventeenO_17293 : Nat.Prime 17293 := by norm_num

private theorem prime_seventeenO_19421 : Nat.Prime 19421 := by norm_num

private theorem prime_seventeenO_19801 : Nat.Prime 19801 := by norm_num

private theorem prime_seventeenO_19891 : Nat.Prime 19891 := by norm_num

private theorem prime_seventeenO_20173 : Nat.Prime 20173 := by norm_num

private theorem prime_seventeenO_22259 : Nat.Prime 22259 := by norm_num

private theorem prime_seventeenO_22409 : Nat.Prime 22409 := by norm_num

private theorem prime_seventeenO_22717 : Nat.Prime 22717 := by norm_num

private theorem prime_seventeenO_23719 : Nat.Prime 23719 := by norm_num

private theorem prime_seventeenO_24923 : Nat.Prime 24923 := by norm_num

private theorem prime_seventeenO_25127 : Nat.Prime 25127 := by norm_num

private theorem prime_seventeenO_25219 : Nat.Prime 25219 := by norm_num

private theorem prime_seventeenO_26759 : Nat.Prime 26759 := by norm_num

private theorem prime_seventeenO_28547 : Nat.Prime 28547 := by norm_num

private theorem prime_seventeenO_29611 : Nat.Prime 29611 := by norm_num

private theorem prime_seventeenO_29641 : Nat.Prime 29641 := by norm_num

private theorem prime_seventeenO_30773 : Nat.Prime 30773 := by norm_num

private theorem prime_seventeenO_30931 : Nat.Prime 30931 := by norm_num

private theorem prime_seventeenO_31319 : Nat.Prime 31319 := by norm_num

private theorem prime_seventeenO_32359 : Nat.Prime 32359 := by norm_num

private theorem prime_seventeenO_35051 : Nat.Prime 35051 := by norm_num

private theorem prime_seventeenO_36217 : Nat.Prime 36217 := by norm_num

private theorem prime_seventeenO_36923 : Nat.Prime 36923 := by norm_num

private theorem prime_seventeenO_37847 : Nat.Prime 37847 := by norm_num

private theorem prime_seventeenO_40163 : Nat.Prime 40163 := by norm_num

private theorem prime_seventeenO_43793 : Nat.Prime 43793 := by norm_num

private theorem prime_seventeenO_45263 : Nat.Prime 45263 := by norm_num

private theorem prime_seventeenO_46133 : Nat.Prime 46133 := by norm_num

private theorem prime_seventeenO_47129 : Nat.Prime 47129 := by norm_num

private theorem prime_seventeenO_48757 : Nat.Prime 48757 := by norm_num

private theorem prime_seventeenO_49171 : Nat.Prime 49171 := by norm_num

private theorem prime_seventeenO_49279 : Nat.Prime 49279 := by norm_num

private theorem prime_seventeenO_49417 : Nat.Prime 49417 := by norm_num

private theorem prime_seventeenO_52127 : Nat.Prime 52127 := by norm_num

private theorem prime_seventeenO_53407 : Nat.Prime 53407 := by norm_num

private theorem prime_seventeenO_54601 : Nat.Prime 54601 := by norm_num

private theorem prime_seventeenO_54833 : Nat.Prime 54833 := by norm_num

private theorem prime_seventeenO_56747 : Nat.Prime 56747 := by norm_num

private theorem prime_seventeenO_59167 : Nat.Prime 59167 := by norm_num

private theorem prime_seventeenO_59359 : Nat.Prime 59359 := by norm_num

private theorem prime_seventeenO_67523 : Nat.Prime 67523 := by norm_num

private theorem prime_seventeenO_76679 : Nat.Prime 76679 := by norm_num

private theorem prime_seventeenO_81637 : Nat.Prime 81637 := by norm_num

private theorem prime_seventeenO_83047 : Nat.Prime 83047 := by norm_num

private theorem prime_seventeenO_84503 : Nat.Prime 84503 := by norm_num

private theorem prime_seventeenO_97259 : Nat.Prime 97259 := by norm_num

private theorem prime_seventeenO_118801 : Nat.Prime 118801 := by norm_num

private theorem prime_seventeenO_127819 : Nat.Prime 127819 := by norm_num

private theorem prime_seventeenO_131849 : Nat.Prime 131849 := by norm_num

private theorem prime_seventeenO_135221 : Nat.Prime 135221 := by norm_num

private theorem prime_seventeenO_136601 : Nat.Prime 136601 := by norm_num

private theorem prime_seventeenO_136657 : Nat.Prime 136657 := by norm_num

private theorem prime_seventeenO_141023 : Nat.Prime 141023 := by norm_num

private theorem prime_seventeenO_144479 : Nat.Prime 144479 := by norm_num

private theorem prime_seventeenO_152027 : Nat.Prime 152027 := by norm_num

private theorem prime_seventeenO_154589 : Nat.Prime 154589 := by norm_num

private theorem prime_seventeenO_159421 : Nat.Prime 159421 := by norm_num

private theorem prime_seventeenO_162917 : Nat.Prime 162917 := by norm_num

private theorem prime_seventeenO_169891 : Nat.Prime 169891 := by norm_num

private theorem prime_seventeenO_171637 : Nat.Prime 171637 := by norm_num

private theorem prime_seventeenO_172307 : Nat.Prime 172307 := by norm_num

private theorem prime_seventeenO_179951 : Nat.Prime 179951 := by norm_num

private theorem prime_seventeenO_180647 : Nat.Prime 180647 := by norm_num

private theorem prime_seventeenO_187477 : Nat.Prime 187477 := by norm_num

private theorem prime_seventeenO_188473 : Nat.Prime 188473 := by norm_num

private theorem prime_seventeenO_197969 : Nat.Prime 197969 := by norm_num

private theorem prime_seventeenO_212081 : Nat.Prime 212081 := by norm_num

private theorem prime_seventeenO_223283 : Nat.Prime 223283 := by norm_num

private theorem prime_seventeenO_236723 : Nat.Prime 236723 := by norm_num

private theorem prime_seventeenO_293827 : Nat.Prime 293827 := by norm_num

private theorem prime_seventeenO_298187 : Nat.Prime 298187 := by norm_num

private theorem prime_seventeenO_299027 : Nat.Prime 299027 := by norm_num

private theorem prime_seventeenO_299311 : Nat.Prime 299311 := by norm_num

private theorem prime_seventeenO_327263 : Nat.Prime 327263 := by norm_num

private theorem prime_seventeenO_327829 : Nat.Prime 327829 := by norm_num

private theorem prime_seventeenO_339557 : Nat.Prime 339557 := by norm_num

private theorem prime_seventeenO_352237 : Nat.Prime 352237 := by norm_num

private theorem prime_seventeenO_353963 : Nat.Prime 353963 := by norm_num

private theorem prime_seventeenO_367849 : Nat.Prime 367849 := by norm_num

private theorem prime_seventeenO_379571 : Nat.Prime 379571 := by norm_num

private theorem prime_seventeenO_391073 : Nat.Prime 391073 := by norm_num

private theorem prime_seventeenO_395293 : Nat.Prime 395293 := by norm_num

private theorem prime_seventeenO_426407 : Nat.Prime 426407 := by norm_num

private theorem prime_seventeenO_439441 : Nat.Prime 439441 := by norm_num

private theorem prime_seventeenO_448843 : Nat.Prime 448843 := by norm_num

private theorem prime_seventeenO_481843 : Nat.Prime 481843 := by norm_num

private theorem prime_seventeenO_489613 : Nat.Prime 489613 := by norm_num

private theorem prime_seventeenO_492839 : Nat.Prime 492839 := by norm_num

private theorem prime_seventeenO_512531 : Nat.Prime 512531 := by norm_num

private theorem prime_seventeenO_528911 : Nat.Prime 528911 := by norm_num

private theorem prime_seventeenO_535937 : Nat.Prime 535937 := by norm_num

private theorem prime_seventeenO_567389 : Nat.Prime 567389 := by norm_num

private theorem prime_seventeenO_572791 : Nat.Prime 572791 := by norm_num

private theorem prime_seventeenO_588881 : Nat.Prime 588881 := by norm_num

private theorem prime_seventeenO_617363 : Nat.Prime 617363 := by norm_num

private theorem prime_seventeenO_619693 : Nat.Prime 619693 := by norm_num

private theorem prime_seventeenO_627481 : Nat.Prime 627481 := by norm_num

private theorem prime_seventeenO_659171 : Nat.Prime 659171 := by norm_num

private theorem prime_seventeenO_763157 : Nat.Prime 763157 := by norm_num

private theorem prime_seventeenO_800873 : Nat.Prime 800873 := by norm_num

private theorem prime_seventeenO_831643 : Nat.Prime 831643 := by norm_num

private theorem prime_seventeenO_865643 : Nat.Prime 865643 := by norm_num

private theorem prime_seventeenO_930409 : Nat.Prime 930409 := by norm_num

private theorem prime_seventeenO_1040857 : Nat.Prime 1040857 := by norm_num

private theorem prime_seventeenO_1066423 : Nat.Prime 1066423 := by norm_num

private theorem prime_seventeenO_1076753 : Nat.Prime 1076753 := by norm_num

private theorem prime_seventeenO_1133689 : Nat.Prime 1133689 := by norm_num

private theorem prime_seventeenO_1142969 : Nat.Prime 1142969 := by norm_num

private theorem prime_seventeenO_1167833 : Nat.Prime 1167833 := by norm_num

private theorem prime_seventeenO_1177751 : Nat.Prime 1177751 := by norm_num

private theorem prime_seventeenO_1231261 : Nat.Prime 1231261 := by norm_num

private theorem prime_seventeenO_1250357 : Nat.Prime 1250357 := by norm_num

private theorem prime_seventeenO_1265981 : Nat.Prime 1265981 := by norm_num

private theorem prime_seventeenO_1340981 : Nat.Prime 1340981 := by norm_num

private theorem prime_seventeenO_1479133 : Nat.Prime 1479133 := by norm_num

private theorem prime_seventeenO_1553471 : Nat.Prime 1553471 := by norm_num

private theorem prime_seventeenO_1563083 : Nat.Prime 1563083 := by norm_num

private theorem prime_seventeenO_1610527 : Nat.Prime 1610527 := by norm_num

private theorem prime_seventeenO_1646189 : Nat.Prime 1646189 := by norm_num

private theorem prime_seventeenO_1675717 : Nat.Prime 1675717 := by norm_num

private theorem prime_seventeenO_1734673 : Nat.Prime 1734673 := by norm_num

private theorem prime_seventeenO_1742063 : Nat.Prime 1742063 := by norm_num

private theorem prime_seventeenO_1744517 : Nat.Prime 1744517 := by norm_num

private theorem prime_seventeenO_1850837 : Nat.Prime 1850837 := by norm_num

private theorem prime_seventeenO_1964323 : Nat.Prime 1964323 := by norm_num

private theorem prime_seventeenO_1996949 : Nat.Prime 1996949 := by norm_num

private theorem prime_seventeenO_2005841 : Nat.Prime 2005841 := by norm_num

private theorem prime_seventeenO_2432869 : Nat.Prime 2432869 := by norm_num

private theorem prime_seventeenO_2577623 : Nat.Prime 2577623 := by norm_num

private theorem prime_seventeenO_2581927 : Nat.Prime 2581927 := by norm_num

private theorem prime_seventeenO_2850187 : Nat.Prime 2850187 := by norm_num

private theorem prime_seventeenO_2882227 : Nat.Prime 2882227 := by norm_num

private theorem prime_seventeenO_3033883 : Nat.Prime 3033883 := by norm_num

private theorem prime_seventeenO_3097169 : Nat.Prime 3097169 := by norm_num

private theorem prime_seventeenO_3332713 : Nat.Prime 3332713 := by norm_num

private theorem prime_seventeenO_3395999 : Nat.Prime 3395999 := by norm_num

private theorem prime_seventeenO_3606989 : Nat.Prime 3606989 := by norm_num

private theorem prime_seventeenO_3735763 : Nat.Prime 3735763 := by norm_num

private theorem prime_seventeenO_3765239 : Nat.Prime 3765239 := by norm_num

private theorem prime_seventeenO_3960137 : Nat.Prime 3960137 := by norm_num

private theorem prime_seventeenO_4193789 : Nat.Prime 4193789 := by norm_num

private theorem prime_seventeenO_4226671 : Nat.Prime 4226671 := by norm_num

private theorem prime_seventeenO_4592543 : Nat.Prime 4592543 := by norm_num

private theorem prime_seventeenO_4930417 : Nat.Prime 4930417 := by norm_num

private theorem prime_seventeenO_5597413 : Nat.Prime 5597413 := by norm_num

private theorem prime_seventeenO_5767283 : Nat.Prime 5767283 := by norm_num

private theorem prime_seventeenO_6757511 : Nat.Prime 6757511 := by norm_num

private theorem prime_seventeenO_6936253 : Nat.Prime 6936253 := by norm_num

private theorem prime_seventeenO_7146757 : Nat.Prime 7146757 := by norm_num

private theorem prime_seventeenO_7303909 : Nat.Prime 7303909 := by norm_num

private theorem prime_seventeenO_7661581 : Nat.Prime 7661581 := by norm_num

private theorem prime_seventeenO_8511353 : Nat.Prime 8511353 := by norm_num

private theorem prime_seventeenO_8574737 : Nat.Prime 8574737 := by norm_num

private theorem prime_seventeenO_8767271 : Nat.Prime 8767271 := by norm_num

private theorem prime_seventeenO_9229411 : Nat.Prime 9229411 := by norm_num

private theorem prime_seventeenO_9923933 : Nat.Prime 9923933 := by norm_num

private theorem prime_seventeenO_9978323 : Nat.Prime 9978323 := by norm_num

private theorem prime_seventeenO_10154951 : Nat.Prime 10154951 := by
  apply lucas_primality 10154951 (7 : ZMod 10154951)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (17, 1), (919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (17, 1), (919, 1)] : List FactorBlock).map factorBlockValue).prod) = 10154951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_seventeenO_919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10154951) ^ 5077475 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10154951) ^ 2030990 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10154951) ^ 781150 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10154951) ^ 597350 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10154951) ^ 11050 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_10307039 : Nat.Prime 10307039 := by
  apply lucas_primality 10307039 (7 : ZMod 10307039)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (461, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (461, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 10307039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_461
      · exact prime_seventeenO_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10307039) ^ 5153519 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10307039) ^ 1472434 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10307039) ^ 22358 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 10307039) ^ 6454 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_11400749 : Nat.Prime 11400749 := by
  apply lucas_primality 11400749 (2 : ZMod 11400749)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2850187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2850187, 1)] : List FactorBlock).map factorBlockValue).prod) = 11400749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_2850187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11400749) ^ 5700374 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11400749) ^ 4 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_11452853 : Nat.Prime 11452853 := by
  apply lucas_primality 11452853 (2 : ZMod 11452853)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (26759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (26759, 1)] : List FactorBlock).map factorBlockValue).prod) = 11452853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_107
      · exact prime_seventeenO_26759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11452853) ^ 5726426 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11452853) ^ 107036 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11452853) ^ 428 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_11713441 : Nat.Prime 11713441 := by
  apply lucas_primality 11713441 (7 : ZMod 11713441)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (23, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (23, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 11713441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11713441) ^ 5856720 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11713441) ^ 3904480 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11713441) ^ 2342688 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11713441) ^ 509280 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 11713441) ^ 11040 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_12825583 : Nat.Prime 12825583 := by
  apply lucas_primality 12825583 (5 : ZMod 12825583)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (23, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) = 12825583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_71
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12825583) ^ 6412791 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 4275194 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 1832226 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 1165962 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 754446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 557634 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 12825583) ^ 180642 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_13251499 : Nat.Prime 13251499 := by
  apply lucas_primality 13251499 (3 : ZMod 13251499)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (169891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (169891, 1)] : List FactorBlock).map factorBlockValue).prod) = 13251499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_169891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13251499) ^ 6625749 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13251499) ^ 4417166 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13251499) ^ 1019346 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 13251499) ^ 78 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_13553807 : Nat.Prime 13553807 := by
  apply lucas_primality 13553807 (5 : ZMod 13553807)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (743, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (743, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 13553807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_743
      · exact prime_seventeenO_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13553807) ^ 6776903 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13553807) ^ 1936258 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13553807) ^ 18242 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13553807) ^ 10402 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_14940509 : Nat.Prime 14940509 := by
  apply lucas_primality 14940509 (2 : ZMod 14940509)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (339557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (339557, 1)] : List FactorBlock).map factorBlockValue).prod) = 14940509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_seventeenO_339557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14940509) ^ 7470254 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940509) ^ 1358228 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14940509) ^ 44 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_16046729 : Nat.Prime 16046729 := by
  apply lucas_primality 16046729 (3 : ZMod 16046729)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2005841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2005841, 1)] : List FactorBlock).map factorBlockValue).prod) = 16046729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_2005841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 16046729) ^ 8023364 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16046729) ^ 8 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_16354049 : Nat.Prime 16354049 := by
  apply lucas_primality 16354049 (3 : ZMod 16354049)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (193, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (193, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 16354049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_193
      · exact prime_seventeenO_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16354049) ^ 8177024 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16354049) ^ 84736 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16354049) ^ 49408 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_16607593 : Nat.Prime 16607593 := by
  apply lucas_primality 16607593 (5 : ZMod 16607593)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (8543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (8543, 1)] : List FactorBlock).map factorBlockValue).prod) = 16607593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_8543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16607593) ^ 8303796 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 16607593) ^ 5535864 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 16607593) ^ 1944 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_21642461 : Nat.Prime 21642461 := by
  apply lucas_primality 21642461 (2 : ZMod 21642461)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21642461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_154589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21642461) ^ 10821230 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21642461) ^ 4328492 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21642461) ^ 3091780 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 21642461) ^ 140 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_22723003 : Nat.Prime 22723003 := by
  apply lucas_primality 22723003 (2 : ZMod 22723003)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) = 22723003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_seventeenO_17293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22723003) ^ 11361501 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22723003) ^ 7574334 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22723003) ^ 311274 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22723003) ^ 1314 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_27745013 : Nat.Prime 27745013 := by
  apply lucas_primality 27745013 (2 : ZMod 27745013)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6936253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6936253, 1)] : List FactorBlock).map factorBlockValue).prod) = 27745013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_6936253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 27745013) ^ 13872506 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27745013) ^ 4 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_28822271 : Nat.Prime 28822271 := by
  apply lucas_primality 28822271 (14 : ZMod 28822271)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2882227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2882227, 1)] : List FactorBlock).map factorBlockValue).prod) = 28822271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_2882227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 28822271) ^ 14411135 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 28822271) ^ 5764454 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 28822271) ^ 10 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_30931477 : Nat.Prime 30931477 := by
  apply lucas_primality 30931477 (2 : ZMod 30931477)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2577623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2577623, 1)] : List FactorBlock).map factorBlockValue).prod) = 30931477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_2577623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30931477) ^ 15465738 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30931477) ^ 10310492 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30931477) ^ 12 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_31268203 : Nat.Prime 31268203 := by
  apply lucas_primality 31268203 (2 : ZMod 31268203)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (43793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (43793, 1)] : List FactorBlock).map factorBlockValue).prod) = 31268203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_seventeenO_43793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31268203) ^ 15634101 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31268203) ^ 10422734 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31268203) ^ 4466886 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31268203) ^ 1839306 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31268203) ^ 714 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_32095471 : Nat.Prime 32095471 := by
  apply lucas_primality 32095471 (3 : ZMod 32095471)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (97259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (97259, 1)] : List FactorBlock).map factorBlockValue).prod) = 32095471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_seventeenO_97259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32095471) ^ 16047735 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32095471) ^ 10698490 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32095471) ^ 6419094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32095471) ^ 2917770 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32095471) ^ 330 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_32896043 : Nat.Prime 32896043 := by
  apply lucas_primality 32896043 (2 : ZMod 32896043)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) = 32896043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_349
      · exact prime_seventeenO_47129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32896043) ^ 16448021 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32896043) ^ 94258 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32896043) ^ 698 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_34598807 : Nat.Prime 34598807 := by
  apply lucas_primality 34598807 (5 : ZMod 34598807)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (491, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (491, 1), (3203, 1)] : List FactorBlock).map factorBlockValue).prod) = 34598807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_491
      · exact prime_seventeenO_3203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 34598807) ^ 17299403 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 34598807) ^ 3145346 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 34598807) ^ 70466 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 34598807) ^ 10802 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_41305951 : Nat.Prime 41305951 := by
  apply lucas_primality 41305951 (3 : ZMod 41305951)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (7, 1), (31, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (7, 1), (31, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 41305951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_t64_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41305951) ^ 20652975 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 13768650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 8261190 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 5900850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 1332450 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 41305951) ^ 878850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_42251813 : Nat.Prime 42251813 := by
  apply lucas_primality 42251813 (2 : ZMod 42251813)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (53, 1), (4861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (53, 1), (4861, 1)] : List FactorBlock).map factorBlockValue).prod) = 42251813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_53
      · exact prime_seventeenO_4861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42251813) ^ 21125906 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42251813) ^ 1030532 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42251813) ^ 797204 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42251813) ^ 8692 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_42615269 : Nat.Prime 42615269 := by
  apply lucas_primality 42615269 (2 : ZMod 42615269)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (9929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (9929, 1)] : List FactorBlock).map factorBlockValue).prod) = 42615269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_37
      · exact prime_seventeenO_9929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42615269) ^ 21307634 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42615269) ^ 1469492 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42615269) ^ 1151764 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42615269) ^ 4292 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_42880543 : Nat.Prime 42880543 := by
  apply lucas_primality 42880543 (3 : ZMod 42880543)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7146757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7146757, 1)] : List FactorBlock).map factorBlockValue).prod) = 42880543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_7146757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 42880543) ^ 21440271 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42880543) ^ 14293514 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42880543) ^ 6 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_45897431 : Nat.Prime 45897431 := by
  apply lucas_primality 45897431 (13 : ZMod 45897431)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (101, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (101, 1), (1567, 1)] : List FactorBlock).map factorBlockValue).prod) = 45897431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_t64_101
      · exact prime_seventeenO_1567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 45897431) ^ 22948715 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 45897431) ^ 9179486 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 45897431) ^ 1582670 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 45897431) ^ 454430 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 45897431) ^ 29290 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_47715119 : Nat.Prime 47715119 := by
  apply lucas_primality 47715119 (7 : ZMod 47715119)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (211, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 47715119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_seventeenO_211
      · exact prime_seventeenO_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47715119) ^ 23857559 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 4337738 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 2511322 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 226138 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 47715119) ^ 88198 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_50928011 : Nat.Prime 50928011 := by
  apply lucas_primality 50928011 (6 : ZMod 50928011)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (631, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (631, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 50928011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_631
      · exact prime_t64_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 50928011) ^ 25464005 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 10185602 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 7275430 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 80710 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 50928011) ^ 44170 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_52142977 : Nat.Prime 52142977 := by
  apply lucas_primality 52142977 (5 : ZMod 52142977)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (45263, 1)] : List FactorBlock).map factorBlockValue).prod) = 52142977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_45263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52142977) ^ 26071488 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 17380992 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 52142977) ^ 1152 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_55490027 : Nat.Prime 55490027 := by
  apply lucas_primality 55490027 (2 : ZMod 55490027)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (27745013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (27745013, 1)] : List FactorBlock).map factorBlockValue).prod) = 55490027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_27745013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 55490027) ^ 27745013 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55490027) ^ 2 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_58978883 : Nat.Prime 58978883 := by
  apply lucas_primality 58978883 (2 : ZMod 58978883)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1734673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1734673, 1)] : List FactorBlock).map factorBlockValue).prod) = 58978883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_seventeenO_1734673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58978883) ^ 29489441 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 58978883) ^ 3469346 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 58978883) ^ 34 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_59878297 : Nat.Prime 59878297 := by
  apply lucas_primality 59878297 (5 : ZMod 59878297)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (831643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (831643, 1)] : List FactorBlock).map factorBlockValue).prod) = 59878297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_831643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 59878297) ^ 29939148 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 59878297) ^ 19959432 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 59878297) ^ 72 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_62602601 : Nat.Prime 62602601 := by
  apply lucas_primality 62602601 (3 : ZMod 62602601)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (89, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 62602601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_89
      · exact prime_seventeenO_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62602601) ^ 31301300 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 12520520 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 703400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62602601) ^ 17800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_73166647 : Nat.Prime 73166647 := by
  apply lucas_primality 73166647 (6 : ZMod 73166647)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1742063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1742063, 1)] : List FactorBlock).map factorBlockValue).prod) = 73166647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_seventeenO_1742063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 73166647) ^ 36583323 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 73166647) ^ 24388882 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 73166647) ^ 10452378 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 73166647) ^ 42 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_73627703 : Nat.Prime 73627703 := by
  apply lucas_primality 73627703 (5 : ZMod 73627703)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5281, 1), (6971, 1)] : List FactorBlock).map factorBlockValue).prod) = 73627703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_5281
      · exact prime_seventeenO_6971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 73627703) ^ 36813851 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 13942 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 73627703) ^ 10562 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_88685873 : Nat.Prime 88685873 := by
  apply lucas_primality 88685873 (3 : ZMod 88685873)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (17, 1), (29641, 1)] : List FactorBlock).map factorBlockValue).prod) = 88685873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_seventeenO_29641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88685873) ^ 44342936 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 8062352 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 5216816 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 88685873) ^ 2992 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_95430239 : Nat.Prime 95430239 := by
  apply lucas_primality 95430239 (7 : ZMod 95430239)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47715119, 1)] : List FactorBlock).map factorBlockValue).prod) = 95430239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_47715119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 95430239) ^ 47715119 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 95430239) ^ 2 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_105207253 : Nat.Prime 105207253 := by
  apply lucas_primality 105207253 (2 : ZMod 105207253)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8767271, 1)] : List FactorBlock).map factorBlockValue).prod) = 105207253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_8767271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 105207253) ^ 52603626 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 35069084 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105207253) ^ 12 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_109178521 : Nat.Prime 109178521 := by
  apply lucas_primality 109178521 (23 : ZMod 109178521)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (107, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 109178521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_107
      · exact prime_seventeenO_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 109178521) ^ 54589260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 36392840 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 21835704 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 9925320 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 1020360 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 109178521) ^ 141240 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_111306893 : Nat.Prime 111306893 := by
  apply lucas_primality 111306893 (2 : ZMod 111306893)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (352237, 1)] : List FactorBlock).map factorBlockValue).prod) = 111306893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_seventeenO_352237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111306893) ^ 55653446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 1408948 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 111306893) ^ 316 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_122594851 : Nat.Prime 122594851 := by
  apply lucas_primality 122594851 (2 : ZMod 122594851)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) = 122594851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_12973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122594851) ^ 61297425 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 40864950 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 24518970 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 17513550 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 122594851) ^ 9450 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_126309679 : Nat.Prime 126309679 := by
  apply lucas_primality 126309679 (3 : ZMod 126309679)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (163, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (163, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 126309679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_59
      · exact prime_t64_163
      · exact prime_seventeenO_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126309679) ^ 63154839 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 126309679) ^ 42103226 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 126309679) ^ 11482698 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 126309679) ^ 2140842 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 126309679) ^ 774906 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 126309679) ^ 634722 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_133252297 : Nat.Prime 133252297 := by
  apply lucas_primality 133252297 (11 : ZMod 133252297)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (191, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (191, 1), (709, 1)] : List FactorBlock).map factorBlockValue).prod) = 133252297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_t64_191
      · exact prime_seventeenO_709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 133252297) ^ 66626148 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 133252297) ^ 44417432 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 133252297) ^ 3250056 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 133252297) ^ 697656 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 133252297) ^ 187944 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_133416637 : Nat.Prime 133416637 := by
  apply lucas_primality 133416637 (6 : ZMod 133416637)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (241, 1), (46133, 1)] : List FactorBlock).map factorBlockValue).prod) = 133416637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_241
      · exact prime_seventeenO_46133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 133416637) ^ 66708318 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 44472212 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 553596 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 133416637) ^ 2892 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_136808989 : Nat.Prime 136808989 := by
  apply lucas_primality 136808989 (2 : ZMod 136808989)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11400749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11400749, 1)] : List FactorBlock).map factorBlockValue).prod) = 136808989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_11400749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 136808989) ^ 68404494 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 136808989) ^ 45602996 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 136808989) ^ 12 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_191642057 : Nat.Prime 191642057 := by
  apply lucas_primality 191642057 (3 : ZMod 191642057)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (43, 1), (109, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (43, 1), (109, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 191642057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_43
      · exact prime_t64_109
      · exact prime_t64_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191642057) ^ 95821028 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191642057) ^ 10086424 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191642057) ^ 4456792 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191642057) ^ 1758184 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191642057) ^ 712424 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_196248589 : Nat.Prime 196248589 := by
  apply lucas_primality 196248589 (2 : ZMod 196248589)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16354049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16354049, 1)] : List FactorBlock).map factorBlockValue).prod) = 196248589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_16354049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 196248589) ^ 98124294 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 196248589) ^ 65416196 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 196248589) ^ 12 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_213122467 : Nat.Prime 213122467 := by
  apply lucas_primality 213122467 (2 : ZMod 213122467)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3089, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3089, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 213122467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_3089
      · exact prime_seventeenO_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 213122467) ^ 106561233 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 71040822 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 68994 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 213122467) ^ 55602 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_241579183 : Nat.Prime 241579183 := by
  apply lucas_primality 241579183 (6 : ZMod 241579183)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3097169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3097169, 1)] : List FactorBlock).map factorBlockValue).prod) = 241579183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_3097169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 241579183) ^ 120789591 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 241579183) ^ 80526394 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 241579183) ^ 18583014 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 241579183) ^ 78 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_255656449 : Nat.Prime 255656449 := by
  apply lucas_primality 255656449 (14 : ZMod 255656449)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (109, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (109, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 255656449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_109
      · exact prime_seventeenO_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 255656449) ^ 127828224 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 255656449) ^ 85218816 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 255656449) ^ 2345472 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 255656449) ^ 502272 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_282861461 : Nat.Prime 282861461 := by
  apply lucas_primality 282861461 (2 : ZMod 282861461)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) = 282861461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_41
      · exact prime_seventeenO_49279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 282861461) ^ 141430730 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 56572292 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 40408780 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 6899060 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 282861461) ^ 5740 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_304357847 : Nat.Prime 304357847 := by
  apply lucas_primality 304357847 (5 : ZMod 304357847)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (19, 1), (83, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (19, 1), (83, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 304357847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_83
      · exact prime_seventeenO_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 304357847) ^ 152178923 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 23412142 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 16018834 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 3666962 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304357847) ^ 533026 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_344755493 : Nat.Prime 344755493 := by
  apply lucas_primality 344755493 (2 : ZMod 344755493)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (971, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 344755493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_seventeenO_971
      · exact prime_seventeenO_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 344755493) ^ 172377746 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 9317716 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 355052 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 344755493) ^ 143708 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_366672217 : Nat.Prime 366672217 := by
  apply lucas_primality 366672217 (5 : ZMod 366672217)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (492839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (492839, 1)] : List FactorBlock).map factorBlockValue).prod) = 366672217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_seventeenO_492839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 366672217) ^ 183336108 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 366672217) ^ 122224072 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 366672217) ^ 11828136 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 366672217) ^ 744 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_393372509 : Nat.Prime 393372509 := by
  apply lucas_primality 393372509 (2 : ZMod 393372509)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (588881, 1)] : List FactorBlock).map factorBlockValue).prod) = 393372509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_167
      · exact prime_seventeenO_588881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 393372509) ^ 196686254 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 2355524 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 393372509) ^ 668 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_399510901 : Nat.Prime 399510901 := by
  apply lucas_primality 399510901 (19 : ZMod 399510901)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (79, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (79, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 399510901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_seventeenO_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 399510901) ^ 199755450 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 399510901) ^ 133170300 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 399510901) ^ 79902180 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 399510901) ^ 5057100 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 399510901) ^ 213300 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_424552907 : Nat.Prime 424552907 := by
  apply lucas_primality 424552907 (2 : ZMod 424552907)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (9229411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (9229411, 1)] : List FactorBlock).map factorBlockValue).prod) = 424552907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_seventeenO_9229411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 424552907) ^ 212276453 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 424552907) ^ 18458822 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 424552907) ^ 46 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_498588301 : Nat.Prime 498588301 := by
  apply lucas_primality 498588301 (10 : ZMod 498588301)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 1), (29, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 1), (29, 1), (2729, 1)] : List FactorBlock).map factorBlockValue).prod) = 498588301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_seventeenO_2729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 498588301) ^ 249294150 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 498588301) ^ 166196100 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 498588301) ^ 99717660 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 498588301) ^ 71226900 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 498588301) ^ 17192700 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 498588301) ^ 182700 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_527998199 : Nat.Prime 527998199 := by
  apply lucas_primality 527998199 (7 : ZMod 527998199)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (59, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (59, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) = 527998199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_seventeenO_49171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 527998199) ^ 263999099 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 527998199) ^ 75428314 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 527998199) ^ 40615246 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 527998199) ^ 8949122 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 527998199) ^ 10738 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_560942329 : Nat.Prime 560942329 := by
  apply lucas_primality 560942329 (7 : ZMod 560942329)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1889, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1889, 1), (12373, 1)] : List FactorBlock).map factorBlockValue).prod) = 560942329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_1889
      · exact prime_seventeenO_12373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 560942329) ^ 280471164 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 560942329) ^ 186980776 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 560942329) ^ 296952 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 560942329) ^ 45336 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_664303721 : Nat.Prime 664303721 := by
  apply lucas_primality 664303721 (3 : ZMod 664303721)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (16607593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (16607593, 1)] : List FactorBlock).map factorBlockValue).prod) = 664303721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_16607593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 664303721) ^ 332151860 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 664303721) ^ 132860744 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 664303721) ^ 40 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_690701213 : Nat.Prime 690701213 := by
  apply lucas_primality 690701213 (2 : ZMod 690701213)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12263, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12263, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) = 690701213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_12263
      · exact prime_seventeenO_14081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 690701213) ^ 345350606 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 690701213) ^ 56324 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 690701213) ^ 49052 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_774668639 : Nat.Prime 774668639 := by
  apply lucas_primality 774668639 (23 : ZMod 774668639)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1663, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) = 774668639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_89
      · exact prime_seventeenO_1663
      · exact prime_seventeenO_2617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 774668639) ^ 387334319 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 8704142 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 465826 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (23 : ZMod 774668639) ^ 296014 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_783928043 : Nat.Prime 783928043 := by
  apply lucas_primality 783928043 (2 : ZMod 783928043)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15727, 1), (24923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15727, 1), (24923, 1)] : List FactorBlock).map factorBlockValue).prod) = 783928043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_15727
      · exact prime_seventeenO_24923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 783928043) ^ 391964021 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 783928043) ^ 49846 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 783928043) ^ 31454 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_830488753 : Nat.Prime 830488753 := by
  apply lucas_primality 830488753 (7 : ZMod 830488753)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5767283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5767283, 1)] : List FactorBlock).map factorBlockValue).prod) = 830488753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_5767283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 830488753) ^ 415244376 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 830488753) ^ 276829584 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 830488753) ^ 144 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_847846819 : Nat.Prime 847846819 := by
  apply lucas_primality 847846819 (7 : ZMod 847846819)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (47, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (47, 1), (3671, 1)] : List FactorBlock).map factorBlockValue).prod) = 847846819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_47
      · exact prime_seventeenO_3671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 847846819) ^ 423923409 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 282615606 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 121120974 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 65218986 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 18039294 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 847846819) ^ 230958 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_867724171 : Nat.Prime 867724171 := by
  apply lucas_primality 867724171 (12 : ZMod 867724171)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (298187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (298187, 1)] : List FactorBlock).map factorBlockValue).prod) = 867724171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_97
      · exact prime_seventeenO_298187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 867724171) ^ 433862085 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 867724171) ^ 289241390 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 867724171) ^ 173544834 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 867724171) ^ 8945610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 867724171) ^ 2910 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_944019971 : Nat.Prime 944019971 := by
  apply lucas_primality 944019971 (10 : ZMod 944019971)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1811, 1), (52127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1811, 1), (52127, 1)] : List FactorBlock).map factorBlockValue).prod) = 944019971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_1811
      · exact prime_seventeenO_52127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 944019971) ^ 472009985 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 944019971) ^ 188803994 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 944019971) ^ 521270 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 944019971) ^ 18110 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_957254689 : Nat.Prime 957254689 := by
  apply lucas_primality 957254689 (14 : ZMod 957254689)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (13, 1), (167, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (13, 1), (167, 1), (1531, 1)] : List FactorBlock).map factorBlockValue).prod) = 957254689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_167
      · exact prime_seventeenO_1531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 957254689) ^ 478627344 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 957254689) ^ 319084896 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 957254689) ^ 73634976 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 957254689) ^ 5732064 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 957254689) ^ 625248 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1030958039 : Nat.Prime 1030958039 := by
  apply lucas_primality 1030958039 (11 : ZMod 1030958039)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (41, 1), (1142969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (41, 1), (1142969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1030958039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_seventeenO_1142969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1030958039) ^ 515479019 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030958039) ^ 93723458 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030958039) ^ 25145318 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030958039) ^ 902 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1037558419 : Nat.Prime 1037558419 := by
  apply lucas_primality 1037558419 (3 : ZMod 1037558419)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (197, 1), (67523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (197, 1), (67523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037558419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_197
      · exact prime_seventeenO_67523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1037558419) ^ 518779209 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037558419) ^ 345852806 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037558419) ^ 79812186 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037558419) ^ 5266794 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037558419) ^ 15366 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1052072531 : Nat.Prime 1052072531 := by
  apply lucas_primality 1052072531 (6 : ZMod 1052072531)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (105207253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1052072531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_105207253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1052072531) ^ 526036265 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 210414506 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1052072531) ^ 10 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1243269197 : Nat.Prime 1243269197 := by
  apply lucas_primality 1243269197 (2 : ZMod 1243269197)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (101, 1), (236723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (101, 1), (236723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243269197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_101
      · exact prime_seventeenO_236723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1243269197) ^ 621634598 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 95636092 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 12309596 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243269197) ^ 5252 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1531464617 : Nat.Prime 1531464617 := by
  apply lucas_primality 1531464617 (3 : ZMod 1531464617)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (101, 1), (172307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531464617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_101
      · exact prime_seventeenO_172307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1531464617) ^ 765732308 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 139224056 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 15163016 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531464617) ^ 8888 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1588277671 : Nat.Prime 1588277671 := by
  apply lucas_primality 1588277671 (7 : ZMod 1588277671)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (43, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588277671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_43
      · exact prime_seventeenO_25127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1588277671) ^ 794138835 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 529425890 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 317655534 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 226896810 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 36936690 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1588277671) ^ 63210 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1811166823 : Nat.Prime 1811166823 := by
  apply lucas_primality 1811166823 (3 : ZMod 1811166823)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (557, 1), (180647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (557, 1), (180647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1811166823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_557
      · exact prime_seventeenO_180647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1811166823) ^ 905583411 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1811166823) ^ 603722274 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1811166823) ^ 3251646 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1811166823) ^ 10026 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1898759389 : Nat.Prime 1898759389 := by
  apply lucas_primality 1898759389 (2 : ZMod 1898759389)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (307, 1), (22409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898759389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_307
      · exact prime_seventeenO_22409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1898759389) ^ 949379694 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 632919796 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 82554756 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 6184884 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1898759389) ^ 84732 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2179651489 : Nat.Prime 2179651489 := by
  apply lucas_primality 2179651489 (19 : ZMod 2179651489)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (23, 1), (141023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179651489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_seventeenO_141023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2179651489) ^ 1089825744 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 726550496 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 311378784 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 94767456 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (19 : ZMod 2179651489) ^ 15456 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2752604287 : Nat.Prime 2752604287 := by
  apply lucas_primality 2752604287 (3 : ZMod 2752604287)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (937, 1), (489613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (937, 1), (489613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2752604287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_937
      · exact prime_seventeenO_489613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2752604287) ^ 1376302143 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752604287) ^ 917534762 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752604287) ^ 2937678 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752604287) ^ 5622 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2951252771 : Nat.Prime 2951252771 := by
  apply lucas_primality 2951252771 (2 : ZMod 2951252771)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (3735763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (3735763, 1)] : List FactorBlock).map factorBlockValue).prod) = 2951252771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_seventeenO_3735763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2951252771) ^ 1475626385 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 590250554 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 37357630 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2951252771) ^ 790 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3544788469 : Nat.Prime 3544788469 := by
  apply lucas_primality 3544788469 (2 : ZMod 3544788469)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (22723003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (22723003, 1)] : List FactorBlock).map factorBlockValue).prod) = 3544788469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_22723003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3544788469) ^ 1772394234 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 1181596156 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 272676036 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3544788469) ^ 156 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3755946823 : Nat.Prime 3755946823 := by
  apply lucas_primality 3755946823 (5 : ZMod 3755946823)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12703, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12703, 1), (49279, 1)] : List FactorBlock).map factorBlockValue).prod) = 3755946823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_12703
      · exact prime_seventeenO_49279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3755946823) ^ 1877973411 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3755946823) ^ 1251982274 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3755946823) ^ 295674 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3755946823) ^ 76218 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3880233977 : Nat.Prime 3880233977 := by
  apply lucas_primality 3880233977 (3 : ZMod 3880233977)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2287, 1), (212081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3880233977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_2287
      · exact prime_seventeenO_212081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3880233977) ^ 1940116988 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 1696648 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3880233977) ^ 18296 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_4232442391 : Nat.Prime 4232442391 := by
  apply lucas_primality 4232442391 (3 : ZMod 4232442391)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (12825583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (12825583, 1)] : List FactorBlock).map factorBlockValue).prod) = 4232442391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_seventeenO_12825583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4232442391) ^ 2116221195 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4232442391) ^ 1410814130 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4232442391) ^ 846488478 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4232442391) ^ 384767490 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4232442391) ^ 330 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_4983623317 : Nat.Prime 4983623317 := by
  apply lucas_primality 4983623317 (11 : ZMod 4983623317)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (1040857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (1040857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4983623317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_seventeenO_1040857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4983623317) ^ 2491811658 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4983623317) ^ 1661207772 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4983623317) ^ 711946188 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4983623317) ^ 262295964 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4983623317) ^ 4788 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_5967429077 : Nat.Prime 5967429077 := by
  apply lucas_primality 5967429077 (2 : ZMod 5967429077)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (213122467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (213122467, 1)] : List FactorBlock).map factorBlockValue).prod) = 5967429077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_213122467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5967429077) ^ 2983714538 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5967429077) ^ 852489868 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5967429077) ^ 28 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_6860556407 : Nat.Prime 6860556407 := by
  apply lucas_primality 6860556407 (5 : ZMod 6860556407)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5839, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5839, 1), (53407, 1)] : List FactorBlock).map factorBlockValue).prod) = 6860556407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_seventeenO_5839
      · exact prime_seventeenO_53407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6860556407) ^ 3430278203 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 623686946 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 1174954 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6860556407) ^ 128458 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_6886286111 : Nat.Prime 6886286111 := by
  apply lucas_primality 6886286111 (11 : ZMod 6886286111)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (62602601, 1)] : List FactorBlock).map factorBlockValue).prod) = 6886286111 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_seventeenO_62602601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6886286111) ^ 3443143055 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 1377257222 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 626026010 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 6886286111) ^ 110 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7237965619 : Nat.Prime 7237965619 := by
  apply lucas_primality 7237965619 (2 : ZMod 7237965619)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (30931477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (30931477, 1)] : List FactorBlock).map factorBlockValue).prod) = 7237965619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_30931477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7237965619) ^ 3618982809 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 2412655206 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 556766586 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7237965619) ^ 234 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7387235899 : Nat.Prime 7387235899 := by
  apply lucas_primality 7387235899 (7 : ZMod 7387235899)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (139, 1), (181, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (139, 1), (181, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) = 7387235899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_139
      · exact prime_seventeenO_181
      · exact prime_seventeenO_6991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7387235899) ^ 3693617949 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387235899) ^ 2462411966 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387235899) ^ 1055319414 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387235899) ^ 53145582 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387235899) ^ 40813458 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7387235899) ^ 1056678 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7738677413 : Nat.Prime 7738677413 := by
  apply lucas_primality 7738677413 (2 : ZMod 7738677413)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1109, 1), (1744517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1109, 1), (1744517, 1)] : List FactorBlock).map factorBlockValue).prod) = 7738677413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_1109
      · exact prime_seventeenO_1744517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7738677413) ^ 3869338706 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7738677413) ^ 6978068 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7738677413) ^ 4436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_8616676351 : Nat.Prime 8616676351 := by
  apply lucas_primality 8616676351 (6 : ZMod 8616676351)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (5659, 1), (10151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (5659, 1), (10151, 1)] : List FactorBlock).map factorBlockValue).prod) = 8616676351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_5659
      · exact prime_seventeenO_10151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8616676351) ^ 4308338175 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 8616676351) ^ 2872225450 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 8616676351) ^ 1723335270 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 8616676351) ^ 1522650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 8616676351) ^ 848850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_8766968939 : Nat.Prime 8766968939 := by
  apply lucas_primality 8766968939 (2 : ZMod 8766968939)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (47, 1), (137, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8766968939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_47
      · exact prime_t64_137
      · exact prime_seventeenO_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8766968939) ^ 4383484469 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1252424134 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 674382226 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 186531254 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 63992474 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8766968939) ^ 1171898 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_9087309221 : Nat.Prime 9087309221 := by
  apply lucas_primality 9087309221 (10 : ZMod 9087309221)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (41305951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (41305951, 1)] : List FactorBlock).map factorBlockValue).prod) = 9087309221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_seventeenO_41305951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 9087309221) ^ 4543654610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 1817461844 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 826119020 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 9087309221) ^ 220 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_9564358091 : Nat.Prime 9564358091 := by
  apply lucas_primality 9564358091 (2 : ZMod 9564358091)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (83, 1), (1646189, 1)] : List FactorBlock).map factorBlockValue).prod) = 9564358091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_83
      · exact prime_seventeenO_1646189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9564358091) ^ 4782179045 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1912871618 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 1366336870 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 115233230 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 9564358091) ^ 5810 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_9663167321 : Nat.Prime 9663167321 := by
  apply lucas_primality 9663167321 (3 : ZMod 9663167321)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (241579183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (241579183, 1)] : List FactorBlock).map factorBlockValue).prod) = 9663167321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_241579183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9663167321) ^ 4831583660 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9663167321) ^ 1932633464 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9663167321) ^ 40 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_11747183939 : Nat.Prime 11747183939 := by
  apply lucas_primality 11747183939 (2 : ZMod 11747183939)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (521, 1), (1610527, 1)] : List FactorBlock).map factorBlockValue).prod) = 11747183939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_521
      · exact prime_seventeenO_1610527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11747183939) ^ 5873591969 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 1678169134 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 22547378 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11747183939) ^ 7294 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_12048401357 : Nat.Prime 12048401357 := by
  apply lucas_primality 12048401357 (2 : ZMod 12048401357)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (11452853, 1)] : List FactorBlock).map factorBlockValue).prod) = 12048401357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_263
      · exact prime_seventeenO_11452853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12048401357) ^ 6024200678 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 45811412 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 12048401357) ^ 1052 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_14565233941 : Nat.Prime 14565233941 := by
  apply lucas_primality 14565233941 (2 : ZMod 14565233941)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (71, 1), (179951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (71, 1), (179951, 1)] : List FactorBlock).map factorBlockValue).prod) = 14565233941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_71
      · exact prime_seventeenO_179951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14565233941) ^ 7282616970 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14565233941) ^ 4855077980 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14565233941) ^ 2913046788 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14565233941) ^ 766591260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14565233941) ^ 205144140 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 14565233941) ^ 80940 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_17230584403 : Nat.Prime 17230584403 := by
  apply lucas_primality 17230584403 (3 : ZMod 17230584403)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (957254689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (957254689, 1)] : List FactorBlock).map factorBlockValue).prod) = 17230584403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_957254689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17230584403) ^ 8615292201 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 17230584403) ^ 5743528134 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 17230584403) ^ 18 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_17605393777 : Nat.Prime 17605393777 := by
  apply lucas_primality 17605393777 (5 : ZMod 17605393777)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (29, 1), (283, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (29, 1), (283, 1), (14897, 1)] : List FactorBlock).map factorBlockValue).prod) = 17605393777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_283
      · exact prime_seventeenO_14897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17605393777) ^ 8802696888 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17605393777) ^ 5868464592 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17605393777) ^ 607082544 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17605393777) ^ 62209872 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17605393777) ^ 1181808 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_18556467049 : Nat.Prime 18556467049 := by
  apply lucas_primality 18556467049 (11 : ZMod 18556467049)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (97, 1), (379571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (97, 1), (379571, 1)] : List FactorBlock).map factorBlockValue).prod) = 18556467049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_97
      · exact prime_seventeenO_379571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18556467049) ^ 9278233524 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 6185489016 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 2650923864 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 191303784 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 18556467049) ^ 48888 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_18577644563 : Nat.Prime 18577644563 := by
  apply lucas_primality 18577644563 (2 : ZMod 18577644563)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (9973, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (9973, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) = 18577644563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_seventeenO_9973
      · exact prime_seventeenO_22717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18577644563) ^ 9288822281 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 453113282 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 1862794 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18577644563) ^ 817786 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_19073603831 : Nat.Prime 19073603831 := by
  apply lucas_primality 19073603831 (7 : ZMod 19073603831)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (31268203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (31268203, 1)] : List FactorBlock).map factorBlockValue).prod) = 19073603831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_seventeenO_31268203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 19073603831) ^ 9536801915 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 19073603831) ^ 3814720766 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 19073603831) ^ 312682030 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 19073603831) ^ 610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_19276921021 : Nat.Prime 19276921021 := by
  apply lucas_primality 19276921021 (6 : ZMod 19276921021)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (45897431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (45897431, 1)] : List FactorBlock).map factorBlockValue).prod) = 19276921021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_45897431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19276921021) ^ 9638460510 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19276921021) ^ 6425640340 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19276921021) ^ 3855384204 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19276921021) ^ 2753845860 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19276921021) ^ 420 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_20699526191 : Nat.Prime 20699526191 := by
  apply lucas_primality 20699526191 (7 : ZMod 20699526191)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (43, 1), (109, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) = 20699526191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_43
      · exact prime_t64_109
      · exact prime_seventeenO_9013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20699526191) ^ 10349763095 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 4139905238 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2957075170 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 481384330 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 189903910 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20699526191) ^ 2296630 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_21764550497 : Nat.Prime 21764550497 := by
  apply lucas_primality 21764550497 (3 : ZMod 21764550497)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (151, 1), (317, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 21764550497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_seventeenO_151
      · exact prime_t64_317
      · exact prime_t64_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21764550497) ^ 10882275248 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 1674196192 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 144136096 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 68657888 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 21764550497) ^ 19912672 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_21934177247 : Nat.Prime 21934177247 := by
  apply lucas_primality 21934177247 (5 : ZMod 21934177247)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1279, 1), (8574737, 1)] : List FactorBlock).map factorBlockValue).prod) = 21934177247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_1279
      · exact prime_seventeenO_8574737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 21934177247) ^ 10967088623 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 17149474 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 21934177247) ^ 2558 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_24733799971 : Nat.Prime 24733799971 := by
  apply lucas_primality 24733799971 (2 : ZMod 24733799971)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 3), (17, 1), (83, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 3), (17, 1), (83, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 24733799971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_83
      · exact prime_t64_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24733799971) ^ 12366899985 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 8244599990 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 4946759994 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 2248527270 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 1454929410 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 297997590 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24733799971) ^ 56341230 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_30059653973 : Nat.Prime 30059653973 := by
  apply lucas_primality 30059653973 (2 : ZMod 30059653973)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (197, 1), (930409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (197, 1), (930409, 1)] : List FactorBlock).map factorBlockValue).prod) = 30059653973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_197
      · exact prime_seventeenO_930409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30059653973) ^ 15029826986 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30059653973) ^ 733162292 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30059653973) ^ 152587076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30059653973) ^ 32308 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_34991366329 : Nat.Prime 34991366329 := by
  apply lucas_primality 34991366329 (7 : ZMod 34991366329)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1373, 1), (353963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1373, 1), (353963, 1)] : List FactorBlock).map factorBlockValue).prod) = 34991366329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_1373
      · exact prime_seventeenO_353963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34991366329) ^ 17495683164 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34991366329) ^ 11663788776 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34991366329) ^ 25485336 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 34991366329) ^ 98856 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_38147207663 : Nat.Prime 38147207663 := by
  apply lucas_primality 38147207663 (5 : ZMod 38147207663)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19073603831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19073603831, 1)] : List FactorBlock).map factorBlockValue).prod) = 38147207663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_19073603831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 38147207663) ^ 19073603831 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 38147207663) ^ 2 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_38346077113 : Nat.Prime 38346077113 := by
  apply lucas_primality 38346077113 (5 : ZMod 38346077113)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (9923933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (9923933, 1)] : List FactorBlock).map factorBlockValue).prod) = 38346077113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_seventeenO_9923933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38346077113) ^ 19173038556 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 38346077113) ^ 12782025704 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 38346077113) ^ 5478011016 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 38346077113) ^ 1667220744 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 38346077113) ^ 3864 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_39568669331 : Nat.Prime 39568669331 := by
  apply lucas_primality 39568669331 (2 : ZMod 39568669331)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1097, 1), (3606989, 1)] : List FactorBlock).map factorBlockValue).prod) = 39568669331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_1097
      · exact prime_seventeenO_3606989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39568669331) ^ 19784334665 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 7913733866 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 36069890 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39568669331) ^ 10970 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_42056266807 : Nat.Prime 42056266807 := by
  apply lucas_primality 42056266807 (6 : ZMod 42056266807)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (277, 1), (118801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (277, 1), (118801, 1)] : List FactorBlock).map factorBlockValue).prod) = 42056266807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_71
      · exact prime_seventeenO_277
      · exact prime_seventeenO_118801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42056266807) ^ 21028133403 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42056266807) ^ 14018755602 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42056266807) ^ 592341786 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42056266807) ^ 151827678 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 42056266807) ^ 354006 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_44846392663 : Nat.Prime 44846392663 := by
  apply lucas_primality 44846392663 (3 : ZMod 44846392663)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (830488753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (830488753, 1)] : List FactorBlock).map factorBlockValue).prod) = 44846392663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_830488753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44846392663) ^ 22423196331 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44846392663) ^ 14948797554 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 44846392663) ^ 54 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_47682293027 : Nat.Prime 47682293027 := by
  apply lucas_primality 47682293027 (2 : ZMod 47682293027)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1759, 1), (13553807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1759, 1), (13553807, 1)] : List FactorBlock).map factorBlockValue).prod) = 47682293027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_1759
      · exact prime_seventeenO_13553807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47682293027) ^ 23841146513 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47682293027) ^ 27107614 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47682293027) ^ 3518 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_49153528429 : Nat.Prime 49153528429 := by
  apply lucas_primality 49153528429 (2 : ZMod 49153528429)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (1061, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 49153528429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_61
      · exact prime_t64_1061
      · exact prime_seventeenO_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49153528429) ^ 24576764214 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 16384509476 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 2587027812 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 805795548 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 46327548 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49153528429) ^ 14756388 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_54703844669 : Nat.Prime 54703844669 := by
  apply lucas_primality 54703844669 (2 : ZMod 54703844669)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1243269197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1243269197, 1)] : List FactorBlock).map factorBlockValue).prod) = 54703844669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_seventeenO_1243269197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54703844669) ^ 27351922334 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54703844669) ^ 4973076788 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 54703844669) ^ 44 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_61671069553 : Nat.Prime 61671069553 := by
  apply lucas_primality 61671069553 (10 : ZMod 61671069553)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (107, 1), (449, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (107, 1), (449, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 61671069553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_t64_107
      · exact prime_seventeenO_449
      · exact prime_seventeenO_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 61671069553) ^ 30835534776 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 61671069553) ^ 20557023184 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 61671069553) ^ 1312150416 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 61671069553) ^ 576365136 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 61671069553) ^ 137352048 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 61671069553) ^ 108385008 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_66228315889 : Nat.Prime 66228315889 := by
  apply lucas_primality 66228315889 (11 : ZMod 66228315889)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (47, 1), (4193789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (47, 1), (4193789, 1)] : List FactorBlock).map factorBlockValue).prod) = 66228315889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_seventeenO_4193789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 66228315889) ^ 33114157944 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 66228315889) ^ 22076105296 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 66228315889) ^ 9461187984 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 66228315889) ^ 1409113104 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 66228315889) ^ 15792 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_71911962181 : Nat.Prime 71911962181 := by
  apply lucas_primality 71911962181 (2 : ZMod 71911962181)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (399510901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (399510901, 1)] : List FactorBlock).map factorBlockValue).prod) = 71911962181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_399510901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71911962181) ^ 35955981090 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71911962181) ^ 23970654060 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71911962181) ^ 14382392436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71911962181) ^ 180 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_96047789699 : Nat.Prime 96047789699 := by
  apply lucas_primality 96047789699 (2 : ZMod 96047789699)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6860556407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6860556407, 1)] : List FactorBlock).map factorBlockValue).prod) = 96047789699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_6860556407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96047789699) ^ 48023894849 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 96047789699) ^ 13721112814 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 96047789699) ^ 14 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_111179436971 : Nat.Prime 111179436971 := by
  apply lucas_primality 111179436971 (2 : ZMod 111179436971)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1588277671, 1)] : List FactorBlock).map factorBlockValue).prod) = 111179436971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_1588277671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111179436971) ^ 55589718485 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 22235887394 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 15882776710 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 111179436971) ^ 70 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_122684585791 : Nat.Prime 122684585791 := by
  apply lucas_primality 122684585791 (6 : ZMod 122684585791)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1051, 1), (299311, 1)] : List FactorBlock).map factorBlockValue).prod) = 122684585791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_1051
      · exact prime_seventeenO_299311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 122684585791) ^ 61342292895 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 40894861930 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 24536917158 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 9437275830 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 116731290 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 122684585791) ^ 409890 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_128102133877 : Nat.Prime 128102133877 := by
  apply lucas_primality 128102133877 (14 : ZMod 128102133877)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (181, 1), (58978883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (181, 1), (58978883, 1)] : List FactorBlock).map factorBlockValue).prod) = 128102133877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_181
      · exact prime_seventeenO_58978883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 128102133877) ^ 64051066938 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 128102133877) ^ 42700711292 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 128102133877) ^ 707746596 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 128102133877) ^ 2172 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_145849248859 : Nat.Prime 145849248859 := by
  apply lucas_primality 145849248859 (3 : ZMod 145849248859)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1627, 1), (14940509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1627, 1), (14940509, 1)] : List FactorBlock).map factorBlockValue).prod) = 145849248859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_1627
      · exact prime_seventeenO_14940509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 145849248859) ^ 72924624429 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 48616416286 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 89643054 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 145849248859) ^ 9762 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_146634385643 : Nat.Prime 146634385643 := by
  apply lucas_primality 146634385643 (2 : ZMod 146634385643)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (187477, 1), (391073, 1)] : List FactorBlock).map factorBlockValue).prod) = 146634385643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_187477
      · exact prime_seventeenO_391073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 146634385643) ^ 73317192821 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 782146 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 146634385643) ^ 374954 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_168225067229 : Nat.Prime 168225067229 := by
  apply lucas_primality 168225067229 (2 : ZMod 168225067229)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (42056266807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (42056266807, 1)] : List FactorBlock).map factorBlockValue).prod) = 168225067229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_42056266807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 168225067229) ^ 84112533614 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 168225067229) ^ 4 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_178433683397 : Nat.Prime 178433683397 := by
  apply lucas_primality 178433683397 (2 : ZMod 178433683397)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (271, 1), (593, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (271, 1), (593, 1), (1997, 1)] : List FactorBlock).map factorBlockValue).prod) = 178433683397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_seventeenO_271
      · exact prime_seventeenO_593
      · exact prime_seventeenO_1997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178433683397) ^ 89216841698 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 178433683397) ^ 1283695564 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 178433683397) ^ 658426876 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 178433683397) ^ 300899972 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 178433683397) ^ 89350868 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_194708329913 : Nat.Prime 194708329913 := by
  apply lucas_primality 194708329913 (3 : ZMod 194708329913)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (191642057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (191642057, 1)] : List FactorBlock).map factorBlockValue).prod) = 194708329913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_127
      · exact prime_seventeenO_191642057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 194708329913) ^ 97354164956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 194708329913) ^ 1533136456 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 194708329913) ^ 1016 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_213499073093 : Nat.Prime 213499073093 := by
  apply lucas_primality 213499073093 (2 : ZMod 213499073093)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1663, 1), (32095471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1663, 1), (32095471, 1)] : List FactorBlock).map factorBlockValue).prod) = 213499073093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_1663
      · exact prime_seventeenO_32095471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 213499073093) ^ 106749536546 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 213499073093) ^ 128381884 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 213499073093) ^ 6652 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_262367120149 : Nat.Prime 262367120149 := by
  apply lucas_primality 262367120149 (14 : ZMod 262367120149)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (727, 1), (1069, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 262367120149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_seventeenO_727
      · exact prime_seventeenO_1069
      · exact prime_seventeenO_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 262367120149) ^ 131183560074 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 87455706716 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 37481017164 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 360890124 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 245432292 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 262367120149) ^ 65281692 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_268254770561 : Nat.Prime 268254770561 := by
  apply lucas_primality 268254770561 (3 : ZMod 268254770561)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (59878297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (59878297, 1)] : List FactorBlock).map factorBlockValue).prod) = 268254770561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_59878297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 268254770561) ^ 134127385280 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 53650954112 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 38322110080 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 268254770561) ^ 4480 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_291003136807 : Nat.Prime 291003136807 := by
  apply lucas_primality 291003136807 (3 : ZMod 291003136807)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131849, 1), (367849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131849, 1), (367849, 1)] : List FactorBlock).map factorBlockValue).prod) = 291003136807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_131849
      · exact prime_seventeenO_367849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 291003136807) ^ 145501568403 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 291003136807) ^ 97001045602 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 291003136807) ^ 2207094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 291003136807) ^ 791094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_319188383753 : Nat.Prime 319188383753 := by
  apply lucas_primality 319188383753 (3 : ZMod 319188383753)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (79, 1), (10307039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (79, 1), (10307039, 1)] : List FactorBlock).map factorBlockValue).prod) = 319188383753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_79
      · exact prime_seventeenO_10307039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 319188383753) ^ 159594191876 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 319188383753) ^ 45598340536 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 319188383753) ^ 4040359288 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 319188383753) ^ 30968 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_338021059213 : Nat.Prime 338021059213 := by
  apply lucas_primality 338021059213 (2 : ZMod 338021059213)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (227, 1), (617363, 1)] : List FactorBlock).map factorBlockValue).prod) = 338021059213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_t64_227
      · exact prime_seventeenO_617363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 338021059213) ^ 169010529606 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 112673686404 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 5045090436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 1489079556 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 338021059213) ^ 547524 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_380626910827 : Nat.Prime 380626910827 := by
  apply lucas_primality 380626910827 (2 : ZMod 380626910827)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (71, 1), (28822271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (71, 1), (28822271, 1)] : List FactorBlock).map factorBlockValue).prod) = 380626910827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_71
      · exact prime_seventeenO_28822271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 380626910827) ^ 190313455413 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 380626910827) ^ 126875636942 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 380626910827) ^ 12278287446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 380626910827) ^ 5360942406 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 380626910827) ^ 13206 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_395043748273 : Nat.Prime 395043748273 := by
  apply lucas_primality 395043748273 (5 : ZMod 395043748273)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (1871, 1), (162917, 1)] : List FactorBlock).map factorBlockValue).prod) = 395043748273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_1871
      · exact prime_seventeenO_162917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 395043748273) ^ 197521874136 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 131681249424 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 211140432 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 395043748273) ^ 2424816 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_426899406397 : Nat.Prime 426899406397 := by
  apply lucas_primality 426899406397 (6 : ZMod 426899406397)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (43, 1), (101, 1), (481843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (43, 1), (101, 1), (481843, 1)] : List FactorBlock).map factorBlockValue).prod) = 426899406397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_43
      · exact prime_t64_101
      · exact prime_seventeenO_481843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 426899406397) ^ 213449703198 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 426899406397) ^ 142299802132 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 426899406397) ^ 25111729788 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 426899406397) ^ 9927893172 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 426899406397) ^ 4226726796 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 426899406397) ^ 885972 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_435674924099 : Nat.Prime 435674924099 := by
  apply lucas_primality 435674924099 (2 : ZMod 435674924099)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (599, 1), (739, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (599, 1), (739, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod) = 435674924099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_151
      · exact prime_seventeenO_599
      · exact prime_seventeenO_739
      · exact prime_seventeenO_3259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435674924099) ^ 217837462049 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 2885264398 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 727337102 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 589546582 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 435674924099) ^ 133683622 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_437178560129 : Nat.Prime 437178560129 := by
  apply lucas_primality 437178560129 (3 : ZMod 437178560129)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (163, 1), (353, 1), (59359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (163, 1), (353, 1), (59359, 1)] : List FactorBlock).map factorBlockValue).prod) = 437178560129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_163
      · exact prime_seventeenO_353
      · exact prime_seventeenO_59359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 437178560129) ^ 218589280064 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 437178560129) ^ 2682077056 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 437178560129) ^ 1238466176 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 437178560129) ^ 7364992 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_504121961207 : Nat.Prime 504121961207 := by
  apply lucas_primality 504121961207 (5 : ZMod 504121961207)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (277, 1), (461, 1), (32359, 1)] : List FactorBlock).map factorBlockValue).prod) = 504121961207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_seventeenO_277
      · exact prime_t64_461
      · exact prime_seventeenO_32359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 504121961207) ^ 252060980603 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 8264294446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1819934878 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 1093540046 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 504121961207) ^ 15579034 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_519434361451 : Nat.Prime 519434361451 := by
  apply lucas_primality 519434361451 (10 : ZMod 519434361451)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (311, 1), (757, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (311, 1), (757, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) = 519434361451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_311
      · exact prime_seventeenO_757
      · exact prime_seventeenO_4903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 519434361451) ^ 259717180725 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 519434361451) ^ 173144787150 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 519434361451) ^ 103886872290 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 519434361451) ^ 1670206950 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 519434361451) ^ 686174850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 519434361451) ^ 105942150 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_536509541123 : Nat.Prime 536509541123 := by
  apply lucas_primality 536509541123 (2 : ZMod 536509541123)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (268254770561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (268254770561, 1)] : List FactorBlock).map factorBlockValue).prod) = 536509541123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_268254770561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 536509541123) ^ 268254770561 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 536509541123) ^ 2 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_538156711957 : Nat.Prime 538156711957 := by
  apply lucas_primality 538156711957 (5 : ZMod 538156711957)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (44846392663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (44846392663, 1)] : List FactorBlock).map factorBlockValue).prod) = 538156711957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_44846392663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 538156711957) ^ 269078355978 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 538156711957) ^ 179385570652 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 538156711957) ^ 12 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_563223568793 : Nat.Prime 563223568793 := by
  apply lucas_primality 563223568793 (3 : ZMod 563223568793)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (227, 1), (271, 1), (30931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (227, 1), (271, 1), (30931, 1)] : List FactorBlock).map factorBlockValue).prod) = 563223568793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_227
      · exact prime_seventeenO_271
      · exact prime_seventeenO_30931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 563223568793) ^ 281611784396 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 15222258616 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 2481161096 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 2078315752 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 563223568793) ^ 18209032 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_636041656519 : Nat.Prime 636041656519 := by
  apply lucas_primality 636041656519 (15 : ZMod 636041656519)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (241, 1), (1471, 1), (13001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (241, 1), (1471, 1), (13001, 1)] : List FactorBlock).map factorBlockValue).prod) = 636041656519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_seventeenO_241
      · exact prime_seventeenO_1471
      · exact prime_seventeenO_13001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 636041656519) ^ 318020828259 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 636041656519) ^ 212013885506 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 636041656519) ^ 27653985066 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 636041656519) ^ 2639176998 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 636041656519) ^ 432387258 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 636041656519) ^ 48922518 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_658941752353 : Nat.Prime 658941752353 := by
  apply lucas_primality 658941752353 (5 : ZMod 658941752353)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (527998199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (527998199, 1)] : List FactorBlock).map factorBlockValue).prod) = 658941752353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_527998199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 658941752353) ^ 329470876176 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 658941752353) ^ 219647250784 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 658941752353) ^ 50687827104 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 658941752353) ^ 1248 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_670346901547 : Nat.Prime 670346901547 := by
  apply lucas_primality 670346901547 (2 : ZMod 670346901547)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10211, 1), (1563083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10211, 1), (1563083, 1)] : List FactorBlock).map factorBlockValue).prod) = 670346901547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_seventeenO_10211
      · exact prime_seventeenO_1563083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 670346901547) ^ 335173450773 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 223448967182 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 95763843078 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 65649486 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 670346901547) ^ 428862 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_915532983913 : Nat.Prime 915532983913 := by
  apply lucas_primality 915532983913 (15 : ZMod 915532983913)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (38147207663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (38147207663, 1)] : List FactorBlock).map factorBlockValue).prod) = 915532983913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_38147207663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 915532983913) ^ 457766491956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 915532983913) ^ 305177661304 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 915532983913) ^ 24 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1016195213701 : Nat.Prime 1016195213701 := by
  apply lucas_primality 1016195213701 (2 : ZMod 1016195213701)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (2203, 1), (512531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (2203, 1), (512531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1016195213701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_2203
      · exact prime_seventeenO_512531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1016195213701) ^ 508097606850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016195213701) ^ 338731737900 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016195213701) ^ 203239042740 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016195213701) ^ 461277900 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1016195213701) ^ 1982700 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1707597625589 : Nat.Prime 1707597625589 := by
  apply lucas_primality 1707597625589 (2 : ZMod 1707597625589)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (426899406397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (426899406397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1707597625589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_426899406397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1707597625589) ^ 853798812794 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1707597625589) ^ 4 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1720623545941 : Nat.Prime 1720623545941 := by
  apply lucas_primality 1720623545941 (21 : ZMod 1720623545941)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (1873, 1), (1177751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (1873, 1), (1177751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1720623545941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_seventeenO_1873
      · exact prime_seventeenO_1177751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 1720623545941) ^ 860311772970 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (21 : ZMod 1720623545941) ^ 573541181980 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (21 : ZMod 1720623545941) ^ 344124709188 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (21 : ZMod 1720623545941) ^ 132355657380 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (21 : ZMod 1720623545941) ^ 918645780 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (21 : ZMod 1720623545941) ^ 1460940 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3331922688673 : Nat.Prime 3331922688673 := by
  apply lucas_primality 3331922688673 (5 : ZMod 3331922688673)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (53, 1), (367, 1), (1223, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (53, 1), (367, 1), (1223, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 3331922688673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_seventeenO_367
      · exact prime_seventeenO_1223
      · exact prime_seventeenO_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3331922688673) ^ 1665961344336 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3331922688673) ^ 1110640896224 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3331922688673) ^ 62866465824 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3331922688673) ^ 9078808416 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3331922688673) ^ 2724384864 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3331922688673) ^ 2283703008 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_5110141175411 : Nat.Prime 5110141175411 := by
  apply lucas_primality 5110141175411 (2 : ZMod 5110141175411)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (30059653973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (30059653973, 1)] : List FactorBlock).map factorBlockValue).prod) = 5110141175411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_seventeenO_30059653973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5110141175411) ^ 2555070587705 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110141175411) ^ 1022028235082 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110141175411) ^ 300596539730 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5110141175411) ^ 170 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_6126952389931 : Nat.Prime 6126952389931 := by
  apply lucas_primality 6126952389931 (2 : ZMod 6126952389931)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (113, 1), (5657, 1), (11833, 1)] : List FactorBlock).map factorBlockValue).prod) = 6126952389931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_113
      · exact prime_seventeenO_5657
      · exact prime_seventeenO_11833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6126952389931) ^ 3063476194965 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 2042317463310 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1225390477986 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 54220817610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 1083074490 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6126952389931) ^ 517785210 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7244372988773 : Nat.Prime 7244372988773 := by
  apply lucas_primality 7244372988773 (2 : ZMod 7244372988773)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (6886286111, 1)] : List FactorBlock).map factorBlockValue).prod) = 7244372988773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_263
      · exact prime_seventeenO_6886286111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7244372988773) ^ 3622186494386 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 27545144444 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244372988773) ^ 1052 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7908989265053 : Nat.Prime 7908989265053 := by
  apply lucas_primality 7908989265053 (2 : ZMod 7908989265053)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (6397, 1), (1850837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7908989265053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_167
      · exact prime_seventeenO_6397
      · exact prime_seventeenO_1850837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7908989265053) ^ 3954494632526 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 47359217156 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 1236359116 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7908989265053) ^ 4273196 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_9956099729759 : Nat.Prime 9956099729759 := by
  apply lucas_primality 9956099729759 (7 : ZMod 9956099729759)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (54703844669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (54703844669, 1)] : List FactorBlock).map factorBlockValue).prod) = 9956099729759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_seventeenO_54703844669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9956099729759) ^ 4978049864879 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 1422299961394 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 765853825366 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 9956099729759) ^ 182 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_10476112925053 : Nat.Prime 10476112925053 := by
  apply lucas_primality 10476112925053 (2 : ZMod 10476112925053)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (291003136807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (291003136807, 1)] : List FactorBlock).map factorBlockValue).prod) = 10476112925053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_291003136807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10476112925053) ^ 5238056462526 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476112925053) ^ 3492037641684 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10476112925053) ^ 36 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_11492716013243 : Nat.Prime 11492716013243 := by
  apply lucas_primality 11492716013243 (2 : ZMod 11492716013243)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (338021059213, 1)] : List FactorBlock).map factorBlockValue).prod) = 11492716013243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_seventeenO_338021059213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11492716013243) ^ 5746358006621 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 676042118426 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11492716013243) ^ 34 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_18076669791347 : Nat.Prime 18076669791347 := by
  apply lucas_primality 18076669791347 (2 : ZMod 18076669791347)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (5653, 1), (3033883, 1)] : List FactorBlock).map factorBlockValue).prod) = 18076669791347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_31
      · exact prime_seventeenO_5653
      · exact prime_seventeenO_3033883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18076669791347) ^ 9038334895673 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 1063333517138 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 583118380366 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 3197712682 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18076669791347) ^ 5958262 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_18107153021773 : Nat.Prime 18107153021773 := by
  apply lucas_primality 18107153021773 (2 : ZMod 18107153021773)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (89, 1), (28547, 1), (197969, 1)] : List FactorBlock).map factorBlockValue).prod) = 18107153021773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_seventeenO_28547
      · exact prime_seventeenO_197969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18107153021773) ^ 9053576510886 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 6035717673924 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 203451157548 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 634292676 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18107153021773) ^ 91464588 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_20710593337979 : Nat.Prime 20710593337979 := by
  apply lucas_primality 20710593337979 (2 : ZMod 20710593337979)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (145849248859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (145849248859, 1)] : List FactorBlock).map factorBlockValue).prod) = 20710593337979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_71
      · exact prime_seventeenO_145849248859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20710593337979) ^ 10355296668989 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20710593337979) ^ 291698497718 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20710593337979) ^ 142 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_62525564649137 : Nat.Prime 62525564649137 := by
  apply lucas_primality 62525564649137 (3 : ZMod 62525564649137)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 2), (7387235899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 2), (7387235899, 1)] : List FactorBlock).map factorBlockValue).prod) = 62525564649137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_seventeenO_7387235899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 62525564649137) ^ 31262782324568 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62525564649137) ^ 2718502810832 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62525564649137) ^ 8464 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_66451830061937 : Nat.Prime 66451830061937 := by
  apply lucas_primality 66451830061937 (3 : ZMod 66451830061937)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (572791, 1), (659171, 1)] : List FactorBlock).map factorBlockValue).prod) = 66451830061937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_seventeenO_572791
      · exact prime_seventeenO_659171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66451830061937) ^ 33225915030968 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 6041075460176 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 116014096 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 66451830061937) ^ 100811216 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_67448907900581 : Nat.Prime 67448907900581 := by
  apply lucas_primality 67448907900581 (2 : ZMod 67448907900581)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (349, 1), (9663167321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (349, 1), (9663167321, 1)] : List FactorBlock).map factorBlockValue).prod) = 67448907900581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_349
      · exact prime_seventeenO_9663167321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67448907900581) ^ 33724453950290 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67448907900581) ^ 13489781580116 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67448907900581) ^ 193263346420 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67448907900581) ^ 6980 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_73507308180701 : Nat.Prime 73507308180701 := by
  apply lucas_primality 73507308180701 (2 : ZMod 73507308180701)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (23, 1), (31, 1), (1030958039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (23, 1), (31, 1), (1030958039, 1)] : List FactorBlock).map factorBlockValue).prod) = 73507308180701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_seventeenO_1030958039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73507308180701) ^ 36753654090350 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 73507308180701) ^ 14701461636140 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 73507308180701) ^ 3195969920900 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 73507308180701) ^ 2371203489700 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 73507308180701) ^ 71300 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_74584367950139 : Nat.Prime 74584367950139 := by
  apply lucas_primality 74584367950139 (2 : ZMod 74584367950139)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (127819, 1), (2581927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (127819, 1), (2581927, 1)] : List FactorBlock).map factorBlockValue).prod) = 74584367950139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_113
      · exact prime_seventeenO_127819
      · exact prime_seventeenO_2581927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74584367950139) ^ 37292183975069 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74584367950139) ^ 660038654426 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74584367950139) ^ 583515502 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 74584367950139) ^ 28887094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_106619097506671 : Nat.Prime 106619097506671 := by
  apply lucas_primality 106619097506671 (12 : ZMod 106619097506671)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (199, 1), (7661581, 1)] : List FactorBlock).map factorBlockValue).prod) = 106619097506671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_seventeenO_199
      · exact prime_seventeenO_7661581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 106619097506671) ^ 53309548753335 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 35539699168890 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 21323819501334 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 15231299643810 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 2881597229910 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 535774359330 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (12 : ZMod 106619097506671) ^ 13916070 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_114655864909423 : Nat.Prime 114655864909423 := by
  apply lucas_primality 114655864909423 (3 : ZMod 114655864909423)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (658941752353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (658941752353, 1)] : List FactorBlock).map factorBlockValue).prod) = 114655864909423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_seventeenO_658941752353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 114655864909423) ^ 57327932454711 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114655864909423) ^ 38218621636474 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114655864909423) ^ 3953650514118 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114655864909423) ^ 174 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_129876803368223 : Nat.Prime 129876803368223 := by
  apply lucas_primality 129876803368223 (5 : ZMod 129876803368223)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (7529, 1), (109178521, 1)] : List FactorBlock).map factorBlockValue).prod) = 129876803368223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_seventeenO_7529
      · exact prime_seventeenO_109178521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129876803368223) ^ 64938401684111 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1644010169218 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 17250206318 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 129876803368223) ^ 1189582 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_140896947156781 : Nat.Prime 140896947156781 := by
  apply lucas_primality 140896947156781 (6 : ZMod 140896947156781)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (101, 1), (419, 1), (55490027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (101, 1), (419, 1), (55490027, 1)] : List FactorBlock).map factorBlockValue).prod) = 140896947156781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_101
      · exact prime_seventeenO_419
      · exact prime_seventeenO_55490027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 140896947156781) ^ 70448473578390 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 46965649052260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 28179389431356 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 1395019278780 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 336269563620 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 140896947156781) ^ 2539140 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_190795957956151 : Nat.Prime 190795957956151 := by
  apply lucas_primality 190795957956151 (6 : ZMod 190795957956151)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (41, 1), (4591, 1), (6757511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (41, 1), (4591, 1), (6757511, 1)] : List FactorBlock).map factorBlockValue).prod) = 190795957956151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_seventeenO_4591
      · exact prime_seventeenO_6757511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 190795957956151) ^ 95397978978075 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190795957956151) ^ 63598652652050 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190795957956151) ^ 38159191591230 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190795957956151) ^ 4653559950150 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190795957956151) ^ 41558692650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190795957956151) ^ 28234650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_211963584708541 : Nat.Prime 211963584708541 := by
  apply lucas_primality 211963584708541 (10 : ZMod 211963584708541)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (168225067229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (168225067229, 1)] : List FactorBlock).map factorBlockValue).prod) = 211963584708541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_168225067229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 211963584708541) ^ 105981792354270 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 211963584708541) ^ 70654528236180 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 211963584708541) ^ 42392716941708 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 211963584708541) ^ 30280512101220 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 211963584708541) ^ 1260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_228014296889441 : Nat.Prime 228014296889441 := by
  apply lucas_primality 228014296889441 (3 : ZMod 228014296889441)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (149, 1), (9564358091, 1)] : List FactorBlock).map factorBlockValue).prod) = 228014296889441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_149
      · exact prime_seventeenO_9564358091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 228014296889441) ^ 114007148444720 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 45602859377888 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 1530297294560 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 228014296889441) ^ 23840 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_468249070338449 : Nat.Prime 468249070338449 := by
  apply lucas_primality 468249070338449 (3 : ZMod 468249070338449)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (347, 1), (12048401357, 1)] : List FactorBlock).map factorBlockValue).prod) = 468249070338449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_347
      · exact prime_seventeenO_12048401357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 468249070338449) ^ 234124535169224 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 66892724334064 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 1349420951984 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 468249070338449) ^ 38864 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_502839550705147 : Nat.Prime 502839550705147 := by
  apply lucas_primality 502839550705147 (2 : ZMod 502839550705147)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19801, 1), (4232442391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19801, 1), (4232442391, 1)] : List FactorBlock).map factorBlockValue).prod) = 502839550705147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_19801
      · exact prime_seventeenO_4232442391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 502839550705147) ^ 251419775352573 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 502839550705147) ^ 167613183568382 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 502839550705147) ^ 25394654346 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 502839550705147) ^ 118806 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_505882358351831 : Nat.Prime 505882358351831 := by
  apply lucas_primality 505882358351831 (13 : ZMod 505882358351831)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (48757, 1), (1037558419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (48757, 1), (1037558419, 1)] : List FactorBlock).map factorBlockValue).prod) = 505882358351831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_48757
      · exact prime_seventeenO_1037558419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 505882358351831) ^ 252941179175915 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 505882358351831) ^ 101176471670366 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 505882358351831) ^ 10375584190 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 505882358351831) ^ 487570 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_540658350927197 : Nat.Prime 540658350927197 := by
  apply lucas_primality 540658350927197 (2 : ZMod 540658350927197)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (159421, 1), (847846819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (159421, 1), (847846819, 1)] : List FactorBlock).map factorBlockValue).prod) = 540658350927197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_159421
      · exact prime_seventeenO_847846819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 540658350927197) ^ 270329175463598 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 540658350927197) ^ 3391387276 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 540658350927197) ^ 637684 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_754643424782869 : Nat.Prime 754643424782869 := by
  apply lucas_primality 754643424782869 (7 : ZMod 754643424782869)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (853, 1), (3880233977, 1)] : List FactorBlock).map factorBlockValue).prod) = 754643424782869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_seventeenO_853
      · exact prime_seventeenO_3880233977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 754643424782869) ^ 377321712391434 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 251547808260956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 39718074988572 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 884693346756 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 754643424782869) ^ 194484 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_953884269611099 : Nat.Prime 953884269611099 := by
  apply lucas_primality 953884269611099 (2 : ZMod 953884269611099)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (179, 1), (347, 1), (349, 1), (136657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (179, 1), (347, 1), (349, 1), (136657, 1)] : List FactorBlock).map factorBlockValue).prod) = 953884269611099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_t64_179
      · exact prime_seventeenO_347
      · exact prime_t64_349
      · exact prime_seventeenO_136657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 953884269611099) ^ 476942134805549 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 136269181373014 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 41473229113526 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 5328962400062 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 2748946021934 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 2733192749602 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 953884269611099) ^ 6980134714 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1067248018209017 : Nat.Prime 1067248018209017 := by
  apply lucas_primality 1067248018209017 (3 : ZMod 1067248018209017)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (71, 1), (38346077113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (71, 1), (38346077113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067248018209017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_71
      · exact prime_seventeenO_38346077113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1067248018209017) ^ 533624009104508 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067248018209017) ^ 152464002601288 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067248018209017) ^ 15031662228296 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1067248018209017) ^ 27832 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2733798320613229 : Nat.Prime 2733798320613229 := by
  apply lucas_primality 2733798320613229 (2 : ZMod 2733798320613229)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (20710593337979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (20710593337979, 1)] : List FactorBlock).map factorBlockValue).prod) = 2733798320613229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_seventeenO_20710593337979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2733798320613229) ^ 1366899160306614 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 911266106871076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 248527120055748 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2733798320613229) ^ 132 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_4125424526678383 : Nat.Prime 4125424526678383 := by
  apply lucas_primality 4125424526678383 (3 : ZMod 4125424526678383)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11149, 1), (61671069553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11149, 1), (61671069553, 1)] : List FactorBlock).map factorBlockValue).prod) = 4125424526678383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_11149
      · exact prime_seventeenO_61671069553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4125424526678383) ^ 2062712263339191 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4125424526678383) ^ 1375141508892794 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4125424526678383) ^ 370026417318 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4125424526678383) ^ 66894 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7570312122546493 : Nat.Prime 7570312122546493 := by
  apply lucas_primality 7570312122546493 (2 : ZMod 7570312122546493)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (149, 1), (34991366329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (149, 1), (34991366329, 1)] : List FactorBlock).map factorBlockValue).prod) = 7570312122546493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_149
      · exact prime_seventeenO_34991366329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7570312122546493) ^ 3785156061273246 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570312122546493) ^ 2523437374182164 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570312122546493) ^ 688210192958772 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570312122546493) ^ 50807463909708 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7570312122546493) ^ 216348 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_8404644125874427 : Nat.Prime 8404644125874427 := by
  apply lucas_primality 8404644125874427 (2 : ZMod 8404644125874427)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (3559, 1), (1531464617, 1)] : List FactorBlock).map factorBlockValue).prod) = 8404644125874427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_257
      · exact prime_seventeenO_3559
      · exact prime_seventeenO_1531464617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8404644125874427) ^ 4202322062937213 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2801548041958142 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 32702895431418 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 2361518439414 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8404644125874427) ^ 5487978 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_15816570652505159 : Nat.Prime 15816570652505159 := by
  apply lucas_primality 15816570652505159 (11 : ZMod 15816570652505159)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (263, 1), (380626910827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (263, 1), (380626910827, 1)] : List FactorBlock).map factorBlockValue).prod) = 15816570652505159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_t64_263
      · exact prime_seventeenO_380626910827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 15816570652505159) ^ 7908285326252579 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 15816570652505159) ^ 200209755095002 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 15816570652505159) ^ 60139051910666 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 15816570652505159) ^ 41554 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_16846201113930689 : Nat.Prime 16846201113930689 := by
  apply lucas_primality 16846201113930689 (3 : ZMod 16846201113930689)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (79, 1), (3331922688673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (79, 1), (3331922688673, 1)] : List FactorBlock).map factorBlockValue).prod) = 16846201113930689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_seventeenO_3331922688673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16846201113930689) ^ 8423100556965344 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16846201113930689) ^ 213243052075072 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16846201113930689) ^ 5056 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_22339030043293591 : Nat.Prime 22339030043293591 := by
  apply lucas_primality 22339030043293591 (6 : ZMod 22339030043293591)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (535937, 1), (126309679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (535937, 1), (126309679, 1)] : List FactorBlock).map factorBlockValue).prod) = 22339030043293591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_seventeenO_535937
      · exact prime_seventeenO_126309679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22339030043293591) ^ 11169515021646795 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 22339030043293591) ^ 7446343347764530 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 22339030043293591) ^ 4467806008658718 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 22339030043293591) ^ 2030820913026690 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 22339030043293591) ^ 41682194070 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 22339030043293591) ^ 176859210 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_28857266712418637 : Nat.Prime 28857266712418637 := by
  apply lucas_primality 28857266712418637 (2 : ZMod 28857266712418637)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (1123, 1), (66228315889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (1123, 1), (66228315889, 1)] : List FactorBlock).map factorBlockValue).prod) = 28857266712418637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_97
      · exact prime_seventeenO_1123
      · exact prime_seventeenO_66228315889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28857266712418637) ^ 14428633356209318 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28857266712418637) ^ 297497594973388 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28857266712418637) ^ 25696586564932 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 28857266712418637) ^ 435724 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_33134036871849091 : Nat.Prime 33134036871849091 := by
  apply lucas_primality 33134036871849091 (3 : ZMod 33134036871849091)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (171637, 1), (42615269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (171637, 1), (42615269, 1)] : List FactorBlock).map factorBlockValue).prod) = 33134036871849091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_151
      · exact prime_seventeenO_171637
      · exact prime_seventeenO_42615269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33134036871849091) ^ 16567018435924545 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33134036871849091) ^ 11044678957283030 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33134036871849091) ^ 6626807374369818 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33134036871849091) ^ 219430707760590 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33134036871849091) ^ 193047168570 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33134036871849091) ^ 777515610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_37774890916250381 : Nat.Prime 37774890916250381 := by
  apply lucas_primality 37774890916250381 (2 : ZMod 37774890916250381)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2063, 1), (915532983913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2063, 1), (915532983913, 1)] : List FactorBlock).map factorBlockValue).prod) = 37774890916250381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_2063
      · exact prime_seventeenO_915532983913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37774890916250381) ^ 18887445458125190 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37774890916250381) ^ 7554978183250076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37774890916250381) ^ 18310659678260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37774890916250381) ^ 41260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_61267804512617837 : Nat.Prime 61267804512617837 := by
  apply lucas_primality 61267804512617837 (2 : ZMod 61267804512617837)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (67, 1), (73, 1), (127, 1), (151, 1), (3332713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (67, 1), (73, 1), (127, 1), (151, 1), (3332713, 1)] : List FactorBlock).map factorBlockValue).prod) = 61267804512617837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_67
      · exact prime_t64_73
      · exact prime_seventeenO_127
      · exact prime_seventeenO_151
      · exact prime_seventeenO_3332713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61267804512617837) ^ 30633902256308918 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 8752543501802548 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 914444843471908 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 839284993323532 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 482423657579668 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 405747049752436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 61267804512617837) ^ 18383762572 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_76546352977170413 : Nat.Prime 76546352977170413 := by
  apply lucas_primality 76546352977170413 (2 : ZMod 76546352977170413)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2733798320613229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2733798320613229, 1)] : List FactorBlock).map factorBlockValue).prod) = 76546352977170413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_2733798320613229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76546352977170413) ^ 38273176488585206 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76546352977170413) ^ 10935193282452916 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76546352977170413) ^ 28 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_87766140659829461 : Nat.Prime 87766140659829461 := by
  apply lucas_primality 87766140659829461 (2 : ZMod 87766140659829461)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (190795957956151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (190795957956151, 1)] : List FactorBlock).map factorBlockValue).prod) = 87766140659829461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_seventeenO_190795957956151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87766140659829461) ^ 43883070329914730 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87766140659829461) ^ 17553228131965892 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87766140659829461) ^ 3815919159123020 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87766140659829461) ^ 460 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_102223266935858869 : Nat.Prime 102223266935858869 := by
  apply lucas_primality 102223266935858869 (2 : ZMod 102223266935858869)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (61, 1), (627481, 1), (11713441, 1)] : List FactorBlock).map factorBlockValue).prod) = 102223266935858869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_61
      · exact prime_seventeenO_627481
      · exact prime_seventeenO_11713441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102223266935858869) ^ 51111633467929434 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 34074422311952956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 5380171943992572 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 1675791261243588 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 162910537428 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 102223266935858869) ^ 8727005748 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_113814267595358257 : Nat.Prime 113814267595358257 := by
  apply lucas_primality 113814267595358257 (5 : ZMod 113814267595358257)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (43, 1), (6126952389931, 1)] : List FactorBlock).map factorBlockValue).prod) = 113814267595358257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_seventeenO_6126952389931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 113814267595358257) ^ 56907133797679128 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 37938089198452752 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 2646843432450192 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 113814267595358257) ^ 18576 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_148047202981516331 : Nat.Prime 148047202981516331 := by
  apply lucas_primality 148047202981516331 (6 : ZMod 148047202981516331)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1487, 1), (9956099729759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1487, 1), (9956099729759, 1)] : List FactorBlock).map factorBlockValue).prod) = 148047202981516331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_1487
      · exact prime_seventeenO_9956099729759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 148047202981516331) ^ 74023601490758165 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 29609440596303266 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 99560997297590 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 148047202981516331) ^ 14870 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_382018399699385413 : Nat.Prime 382018399699385413 := by
  apply lucas_primality 382018399699385413 (2 : ZMod 382018399699385413)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (347, 1), (536509541123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (347, 1), (536509541123, 1)] : List FactorBlock).map factorBlockValue).prod) = 382018399699385413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_seventeenO_347
      · exact prime_seventeenO_536509541123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 382018399699385413) ^ 191009199849692706 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 127339466566461804 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 20106231563125548 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 1100917578384396 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 382018399699385413) ^ 712044 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_504051854825488309 : Nat.Prime 504051854825488309 := by
  apply lucas_primality 504051854825488309 (13 : ZMod 504051854825488309)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (277, 1), (49417, 1), (133416637, 1)] : List FactorBlock).map factorBlockValue).prod) = 504051854825488309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_seventeenO_277
      · exact prime_seventeenO_49417
      · exact prime_seventeenO_133416637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 504051854825488309) ^ 252025927412744154 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 168017284941829436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 21915298035890796 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 1819681786373604 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 10199968731924 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (13 : ZMod 504051854825488309) ^ 3778028484 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_682885605572149543 : Nat.Prime 682885605572149543 := by
  apply lucas_primality 682885605572149543 (3 : ZMod 682885605572149543)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113814267595358257, 1)] : List FactorBlock).map factorBlockValue).prod) = 682885605572149543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_113814267595358257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 682885605572149543) ^ 341442802786074771 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 227628535190716514 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 682885605572149543) ^ 6 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_728140395727948727 : Nat.Prime 728140395727948727 := by
  apply lucas_primality 728140395727948727 (5 : ZMod 728140395727948727)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42251813, 1), (8616676351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42251813, 1), (8616676351, 1)] : List FactorBlock).map factorBlockValue).prod) = 728140395727948727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_42251813
      · exact prime_seventeenO_8616676351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 728140395727948727) ^ 364070197863974363 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 728140395727948727) ^ 17233352702 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 728140395727948727) ^ 84503626 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_978072529592328853 : Nat.Prime 978072529592328853 := by
  apply lucas_primality 978072529592328853 (15 : ZMod 978072529592328853)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (211, 1), (2411, 1), (14565233941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (211, 1), (2411, 1), (14565233941, 1)] : List FactorBlock).map factorBlockValue).prod) = 978072529592328853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_seventeenO_211
      · exact prime_seventeenO_2411
      · exact prime_seventeenO_14565233941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 978072529592328853) ^ 489036264796164426 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 978072529592328853) ^ 326024176530776284 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 978072529592328853) ^ 88915684508393532 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 978072529592328853) ^ 4635414832191132 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 978072529592328853) ^ 405670895724732 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (15 : ZMod 978072529592328853) ^ 67151172 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1247760168138177973 : Nat.Prime 1247760168138177973 := by
  apply lucas_primality 1247760168138177973 (2 : ZMod 1247760168138177973)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1663, 1), (62525564649137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1663, 1), (62525564649137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1247760168138177973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_1663
      · exact prime_seventeenO_62525564649137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1247760168138177973) ^ 623880084069088986 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247760168138177973) ^ 415920056046059324 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247760168138177973) ^ 750306775789644 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1247760168138177973) ^ 19956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1522286271594231449 : Nat.Prime 1522286271594231449 := by
  apply lucas_primality 1522286271594231449 (3 : ZMod 1522286271594231449)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1066423, 1), (178433683397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1066423, 1), (178433683397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1522286271594231449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_1066423
      · exact prime_seventeenO_178433683397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1522286271594231449) ^ 761143135797115724 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1522286271594231449) ^ 1427469467176 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1522286271594231449) ^ 8531384 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2292948351215470321 : Nat.Prime 2292948351215470321 := by
  apply lucas_primality 2292948351215470321 (11 : ZMod 2292948351215470321)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (502839550705147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (502839550705147, 1)] : List FactorBlock).map factorBlockValue).prod) = 2292948351215470321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_seventeenO_502839550705147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2292948351215470321) ^ 1146474175607735160 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2292948351215470321) ^ 764316117071823440 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2292948351215470321) ^ 458589670243094064 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2292948351215470321) ^ 120681492169235280 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2292948351215470321) ^ 4560 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2501971364848882193 : Nat.Prime 2501971364848882193 := by
  apply lucas_primality 2501971364848882193 (3 : ZMod 2501971364848882193)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (22339030043293591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (22339030043293591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2501971364848882193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_seventeenO_22339030043293591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2501971364848882193) ^ 1250985682424441096 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2501971364848882193) ^ 357424480692697456 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2501971364848882193) ^ 112 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3379627908495294503 : Nat.Prime 3379627908495294503 := by
  apply lucas_primality 3379627908495294503 (5 : ZMod 3379627908495294503)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7411, 1), (228014296889441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3379627908495294503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_7411
      · exact prime_seventeenO_228014296889441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3379627908495294503) ^ 1689813954247647251 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 456028593778882 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3379627908495294503) ^ 14822 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_6533831533403812223 : Nat.Prime 6533831533403812223 := by
  apply lucas_primality 6533831533403812223 (5 : ZMod 6533831533403812223)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2357, 1), (106619097506671, 1)] : List FactorBlock).map factorBlockValue).prod) = 6533831533403812223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_seventeenO_2357
      · exact prime_seventeenO_106619097506671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6533831533403812223) ^ 3266915766701906111 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 502602425646447094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 2772096535173446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6533831533403812223) ^ 61282 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_9866150589381930971 : Nat.Prime 9866150589381930971 := by
  apply lucas_primality 9866150589381930971 (6 : ZMod 9866150589381930971)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (251, 1), (997, 1), (563223568793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (251, 1), (997, 1), (563223568793, 1)] : List FactorBlock).map factorBlockValue).prod) = 9866150589381930971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_251
      · exact prime_t64_997
      · exact prime_seventeenO_563223568793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9866150589381930971) ^ 4933075294690965485 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 1973230117876386194 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 1409450084197418710 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 39307372866063470 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 9895838103693010 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9866150589381930971) ^ 17517290 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_10444644690637027181 : Nat.Prime 10444644690637027181 := by
  apply lucas_primality 10444644690637027181 (2 : ZMod 10444644690637027181)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (16846201113930689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (16846201113930689, 1)] : List FactorBlock).map factorBlockValue).prod) = 10444644690637027181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_seventeenO_16846201113930689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10444644690637027181) ^ 5222322345318513590 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10444644690637027181) ^ 2088928938127405436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10444644690637027181) ^ 336924022278613780 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10444644690637027181) ^ 620 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_22921103981963124781 : Nat.Prime 22921103981963124781 := by
  apply lucas_primality 22921103981963124781 (2 : ZMod 22921103981963124781)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (382018399699385413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (382018399699385413, 1)] : List FactorBlock).map factorBlockValue).prod) = 22921103981963124781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_382018399699385413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22921103981963124781) ^ 11460551990981562390 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 7640367993987708260 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 4584220796392624956 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 22921103981963124781) ^ 60 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_24045833025727229903 : Nat.Prime 24045833025727229903 := by
  apply lucas_primality 24045833025727229903 (5 : ZMod 24045833025727229903)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (5597413, 1), (4983623317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (5597413, 1), (4983623317, 1)] : List FactorBlock).map factorBlockValue).prod) = 24045833025727229903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_431
      · exact prime_seventeenO_5597413
      · exact prime_seventeenO_4983623317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24045833025727229903) ^ 12022916512863614951 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24045833025727229903) ^ 55790795883357842 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24045833025727229903) ^ 4295883299254 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 24045833025727229903) ^ 4824970006 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_31255574362747278433 : Nat.Prime 31255574362747278433 := by
  apply lucas_primality 31255574362747278433 (5 : ZMod 31255574362747278433)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (83, 1), (18076669791347, 1)] : List FactorBlock).map factorBlockValue).prod) = 31255574362747278433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_t64_83
      · exact prime_seventeenO_18076669791347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31255574362747278433) ^ 15627787181373639216 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 10418524787582426144 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 4465082051821039776 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1008244334282170272 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 376573185093340704 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 31255574362747278433) ^ 1729056 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_47004755940671233151 : Nat.Prime 47004755940671233151 := by
  apply lucas_primality 47004755940671233151 (17 : ZMod 47004755940671233151)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (3779, 1), (6287, 1), (39568669331, 1)] : List FactorBlock).map factorBlockValue).prod) = 47004755940671233151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_3779
      · exact prime_seventeenO_6287
      · exact prime_seventeenO_39568669331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 47004755940671233151) ^ 23502377970335616575 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 9400951188134246630 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 12438411204199850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 7476500070092450 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (17 : ZMod 47004755940671233151) ^ 1187928650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_48091666051454459807 : Nat.Prime 48091666051454459807 := by
  apply lucas_primality 48091666051454459807 (5 : ZMod 48091666051454459807)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24045833025727229903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24045833025727229903, 1)] : List FactorBlock).map factorBlockValue).prod) = 48091666051454459807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_24045833025727229903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48091666051454459807) ^ 24045833025727229903 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48091666051454459807) ^ 2 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_55292668615692560431 : Nat.Prime 55292668615692560431 := by
  apply lucas_primality 55292668615692560431 (7 : ZMod 55292668615692560431)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (87766140659829461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (87766140659829461, 1)] : List FactorBlock).map factorBlockValue).prod) = 55292668615692560431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_87766140659829461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 55292668615692560431) ^ 27646334307846280215 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 55292668615692560431) ^ 18430889538564186810 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 55292668615692560431) ^ 11058533723138512086 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 55292668615692560431) ^ 7898952659384651490 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 55292668615692560431) ^ 630 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_57396967734356186759 : Nat.Prime 57396967734356186759 := by
  apply lucas_primality 57396967734356186759 (7 : ZMod 57396967734356186759)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1247760168138177973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1247760168138177973, 1)] : List FactorBlock).map factorBlockValue).prod) = 57396967734356186759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_seventeenO_1247760168138177973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 57396967734356186759) ^ 28698483867178093379 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 57396967734356186759) ^ 2495520336276355946 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 57396967734356186759) ^ 46 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_85992210770920657639 : Nat.Prime 85992210770920657639 := by
  apply lucas_primality 85992210770920657639 (3 : ZMod 85992210770920657639)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (163, 1), (677, 1), (129876803368223, 1)] : List FactorBlock).map factorBlockValue).prod) = 85992210770920657639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_163
      · exact prime_seventeenO_677
      · exact prime_seventeenO_129876803368223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85992210770920657639) ^ 42996105385460328819 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 28664070256973552546 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 527559575281721826 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 127019513694122094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85992210770920657639) ^ 662106 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_88594225511214335221 : Nat.Prime 88594225511214335221 := by
  apply lucas_primality 88594225511214335221 (10 : ZMod 88594225511214335221)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (31, 1), (353, 1), (194708329913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (11, 1), (31, 1), (353, 1), (194708329913, 1)] : List FactorBlock).map factorBlockValue).prod) = 88594225511214335221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_31
      · exact prime_seventeenO_353
      · exact prime_seventeenO_194708329913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 88594225511214335221) ^ 44297112755607167610 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 29531408503738111740 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 17718845102242867044 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 12656317930173476460 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 8054020501019485020 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 2857878242297236620 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 250975143091258740 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (10 : ZMod 88594225511214335221) ^ 455009940 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_137526623891778748687 : Nat.Prime 137526623891778748687 := by
  apply lucas_primality 137526623891778748687 (3 : ZMod 137526623891778748687)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22921103981963124781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22921103981963124781, 1)] : List FactorBlock).map factorBlockValue).prod) = 137526623891778748687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_22921103981963124781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 137526623891778748687) ^ 68763311945889374343 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 137526623891778748687) ^ 45842207963926249562 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 137526623891778748687) ^ 6 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_179342389870853805599 : Nat.Prime 179342389870853805599 := by
  apply lucas_primality 179342389870853805599 (11 : ZMod 179342389870853805599)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (136601, 1), (7908989265053, 1)] : List FactorBlock).map factorBlockValue).prod) = 179342389870853805599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_83
      · exact prime_seventeenO_136601
      · exact prime_seventeenO_7908989265053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 179342389870853805599) ^ 89671194935426902799 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 2160751685191009706 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 1312892217998798 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179342389870853805599) ^ 22675766 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_208892893812740543621 : Nat.Prime 208892893812740543621 := by
  apply lucas_primality 208892893812740543621 (3 : ZMod 208892893812740543621)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (10444644690637027181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (10444644690637027181, 1)] : List FactorBlock).map factorBlockValue).prod) = 208892893812740543621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_seventeenO_10444644690637027181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208892893812740543621) ^ 104446446906370271810 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 208892893812740543621) ^ 41778578762548108724 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 208892893812740543621) ^ 20 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_217219443529608792893 : Nat.Prime 217219443529608792893 := by
  apply lucas_primality 217219443529608792893 (2 : ZMod 217219443529608792893)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (197, 1), (4363, 1), (1707597625589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (197, 1), (4363, 1), (1707597625589, 1)] : List FactorBlock).map factorBlockValue).prod) = 217219443529608792893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_197
      · exact prime_seventeenO_4363
      · exact prime_seventeenO_1707597625589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217219443529608792893) ^ 108609721764804396446 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 217219443529608792893) ^ 5870795771070507916 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 217219443529608792893) ^ 1102636769185831436 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 217219443529608792893) ^ 49786716371672884 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 217219443529608792893) ^ 127207628 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_270539505267134450701 : Nat.Prime 270539505267134450701 := by
  apply lucas_primality 270539505267134450701 (11 : ZMod 270539505267134450701)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1675717, 1), (538156711957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1675717, 1), (538156711957, 1)] : List FactorBlock).map factorBlockValue).prod) = 270539505267134450701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_seventeenO_1675717
      · exact prime_seventeenO_538156711957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 270539505267134450701) ^ 135269752633567225350 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 270539505267134450701) ^ 90179835089044816900 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 270539505267134450701) ^ 54107901053426890140 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 270539505267134450701) ^ 161447013587100 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 270539505267134450701) ^ 502715100 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_443831096543292924709 : Nat.Prime 443831096543292924709 := by
  apply lucas_primality 443831096543292924709 (2 : ZMod 443831096543292924709)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (8511353, 1), (395043748273, 1)] : List FactorBlock).map factorBlockValue).prod) = 443831096543292924709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_seventeenO_8511353
      · exact prime_seventeenO_395043748273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 443831096543292924709) ^ 221915548271646462354 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 147943698847764308236 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 40348281503935720428 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 52145774772036 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 443831096543292924709) ^ 1123498596 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_675283202967241661693 : Nat.Prime 675283202967241661693 := by
  apply lucas_primality 675283202967241661693 (2 : ZMod 675283202967241661693)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9087309221, 1), (18577644563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9087309221, 1), (18577644563, 1)] : List FactorBlock).map factorBlockValue).prod) = 675283202967241661693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_9087309221
      · exact prime_seventeenO_18577644563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 675283202967241661693) ^ 337641601483620830846 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 675283202967241661693) ^ 74310578252 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 675283202967241661693) ^ 36349236884 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_840302021920015759849 : Nat.Prime 840302021920015759849 := by
  apply lucas_primality 840302021920015759849 (7 : ZMod 840302021920015759849)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (1522286271594231449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (1522286271594231449, 1)] : List FactorBlock).map factorBlockValue).prod) = 840302021920015759849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_seventeenO_1522286271594231449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 840302021920015759849) ^ 420151010960007879924 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 840302021920015759849) ^ 280100673973338586616 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 840302021920015759849) ^ 36534870518261554776 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 840302021920015759849) ^ 552 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3046823232694638117577 : Nat.Prime 3046823232694638117577 := by
  apply lucas_primality 3046823232694638117577 (7 : ZMod 3046823232694638117577)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (197, 1), (1479133, 1), (435674924099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (197, 1), (1479133, 1), (435674924099, 1)] : List FactorBlock).map factorBlockValue).prod) = 3046823232694638117577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_197
      · exact prime_seventeenO_1479133
      · exact prime_seventeenO_435674924099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3046823232694638117577) ^ 1523411616347319058788 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 1015607744231546039192 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 15466107780175828008 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 2059871041140072 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3046823232694638117577) ^ 6993340824 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7220770109780931952291 : Nat.Prime 7220770109780931952291 := by
  apply lucas_primality 7220770109780931952291 (2 : ZMod 7220770109780931952291)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (15913, 1), (1964323, 1), (366672217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (15913, 1), (1964323, 1), (366672217, 1)] : List FactorBlock).map factorBlockValue).prod) = 7220770109780931952291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_15913
      · exact prime_seventeenO_1964323
      · exact prime_seventeenO_366672217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7220770109780931952291) ^ 3610385054890465976145 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 2406923369926977317430 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 1444154021956186390458 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 1031538587111561707470 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 453765481667877330 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 3675958643146230 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7220770109780931952291) ^ 19692711296370 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7240383469162719667139 : Nat.Prime 7240383469162719667139 := by
  apply lucas_primality 7240383469162719667139 (2 : ZMod 7240383469162719667139)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (6427, 1), (33134036871849091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (6427, 1), (33134036871849091, 1)] : List FactorBlock).map factorBlockValue).prod) = 7240383469162719667139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_seventeenO_6427
      · exact prime_seventeenO_33134036871849091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7240383469162719667139) ^ 3620191734581359833569 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7240383469162719667139) ^ 425904909950748215714 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7240383469162719667139) ^ 1126557253642869094 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7240383469162719667139) ^ 218518 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_10063725055916813776837 : Nat.Prime 10063725055916813776837 := by
  apply lucas_primality 10063725055916813776837 (2 : ZMod 10063725055916813776837)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (41, 1), (59167, 1), (10476112925053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (41, 1), (59167, 1), (10476112925053, 1)] : List FactorBlock).map factorBlockValue).prod) = 10063725055916813776837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_seventeenO_59167
      · exact prime_seventeenO_10476112925053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10063725055916813776837) ^ 5031862527958406888418 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10063725055916813776837) ^ 3354575018638937925612 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10063725055916813776837) ^ 914884095992437616076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10063725055916813776837) ^ 245456708680897896996 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10063725055916813776837) ^ 170090169451160508 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10063725055916813776837) ^ 960635412 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_23784406505979643974407 : Nat.Prime 23784406505979643974407 := by
  apply lucas_primality 23784406505979643974407 (5 : ZMod 23784406505979643974407)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (47004755940671233151, 1)] : List FactorBlock).map factorBlockValue).prod) = 23784406505979643974407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_seventeenO_47004755940671233151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 23784406505979643974407) ^ 11892203252989821987203 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 2162218773270876724946 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 1034104630694767129322 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 23784406505979643974407) ^ 506 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_39888734144558519737813 : Nat.Prime 39888734144558519737813 := by
  apply lucas_primality 39888734144558519737813 (2 : ZMod 39888734144558519737813)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (137, 1), (1327, 1), (426407, 1), (424552907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (137, 1), (1327, 1), (426407, 1), (424552907, 1)] : List FactorBlock).map factorBlockValue).prod) = 39888734144558519737813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_101
      · exact prime_t64_137
      · exact prime_seventeenO_1327
      · exact prime_seventeenO_426407
      · exact prime_seventeenO_424552907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39888734144558519737813) ^ 19944367072279259868906 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 13296244714852839912604 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 394937961827312076612 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 291158643390938100276 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 30059332437497000556 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 93546152254907916 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 39888734144558519737813) ^ 93954683825916 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_48277002932255897663783 : Nat.Prime 48277002932255897663783 := by
  apply lucas_primality 48277002932255897663783 (5 : ZMod 48277002932255897663783)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83047, 1), (13251499, 1), (21934177247, 1)] : List FactorBlock).map factorBlockValue).prod) = 48277002932255897663783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_83047
      · exact prime_seventeenO_13251499
      · exact prime_seventeenO_21934177247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48277002932255897663783) ^ 24138501466127948831891 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 581321455708886506 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 3643135235663218 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48277002932255897663783) ^ 2200994474906 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_72311722294671851954153 : Nat.Prime 72311722294671851954153 := by
  apply lucas_primality 72311722294671851954153 (3 : ZMod 72311722294671851954153)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (461, 1), (81637, 1), (5110141175411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (461, 1), (81637, 1), (5110141175411, 1)] : List FactorBlock).map factorBlockValue).prod) = 72311722294671851954153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_t64_461
      · exact prime_seventeenO_81637
      · exact prime_seventeenO_5110141175411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72311722294671851954153) ^ 36155861147335925977076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72311722294671851954153) ^ 1538547282865358552216 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72311722294671851954153) ^ 156858399771522455432 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72311722294671851954153) ^ 885771430781041096 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 72311722294671851954153) ^ 14150631032 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_148634731511732486431051 : Nat.Prime 148634731511732486431051 := by
  apply lucas_primality 148634731511732486431051 (2 : ZMod 148634731511732486431051)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (53, 1), (499, 1), (4243, 1), (519434361451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (53, 1), (499, 1), (4243, 1), (519434361451, 1)] : List FactorBlock).map factorBlockValue).prod) = 148634731511732486431051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_53
      · exact prime_t64_499
      · exact prime_seventeenO_4243
      · exact prime_seventeenO_519434361451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148634731511732486431051) ^ 74317365755866243215525 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 49544910503910828810350 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 29726946302346497286210 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 8743219500690146260650 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 2804428896447782762850 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 297865193410285543950 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 35030575421101222350 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 148634731511732486431051) ^ 286147283550 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_379360834838580191538187 : Nat.Prime 379360834838580191538187 := by
  apply lucas_primality 379360834838580191538187 (2 : ZMod 379360834838580191538187)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 4), (498588301, 1), (17605393777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 4), (498588301, 1), (17605393777, 1)] : List FactorBlock).map factorBlockValue).prod) = 379360834838580191538187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_seventeenO_498588301
      · exact prime_seventeenO_17605393777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 379360834838580191538187) ^ 189680417419290095769093 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 379360834838580191538187) ^ 126453611612860063846062 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 379360834838580191538187) ^ 54194404976940027362598 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 379360834838580191538187) ^ 760869908254386 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (2 : ZMod 379360834838580191538187) ^ 21547989192618 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_449330137038854874752809 : Nat.Prime 449330137038854874752809 := by
  apply lucas_primality 449330137038854874752809 (7 : ZMod 449330137038854874752809)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (599, 1), (31255574362747278433, 1)] : List FactorBlock).map factorBlockValue).prod) = 449330137038854874752809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_599
      · exact prime_seventeenO_31255574362747278433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 449330137038854874752809) ^ 224665068519427437376404 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 149776712346284958250936 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 750133784705934682392 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 449330137038854874752809) ^ 14376 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1719587357096849636181823 : Nat.Prime 1719587357096849636181823 := by
  apply lucas_primality 1719587357096849636181823 (5 : ZMod 1719587357096849636181823)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6827, 1), (95430239, 1), (146634385643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1719587357096849636181823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_seventeenO_6827
      · exact prime_seventeenO_95430239
      · exact prime_seventeenO_146634385643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1719587357096849636181823) ^ 859793678548424818090911 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 573195785698949878727274 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 251880380415533856186 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 18019313114125698 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1719587357096849636181823) ^ 11727040349754 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_2098625564346661642235893 : Nat.Prime 2098625564346661642235893 := by
  apply lucas_primality 2098625564346661642235893 (5 : ZMod 2098625564346661642235893)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (5867, 1), (2292948351215470321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (5867, 1), (2292948351215470321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2098625564346661642235893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_seventeenO_5867
      · exact prime_seventeenO_2292948351215470321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2098625564346661642235893) ^ 1049312782173330821117946 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2098625564346661642235893) ^ 699541854782220547411964 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2098625564346661642235893) ^ 161432735718973972479684 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2098625564346661642235893) ^ 357699942789613370076 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2098625564346661642235893) ^ 915252 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_3538474829180982138678371 : Nat.Prime 3538474829180982138678371 := by
  apply lucas_primality 3538474829180982138678371 (7 : ZMod 3538474829180982138678371)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1123, 1), (944019971, 1), (47682293027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1123, 1), (944019971, 1), (47682293027, 1)] : List FactorBlock).map factorBlockValue).prod) = 3538474829180982138678371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_1123
      · exact prime_seventeenO_944019971
      · exact prime_seventeenO_47682293027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3538474829180982138678371) ^ 1769237414590491069339185 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3538474829180982138678371) ^ 707694965836196427735674 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3538474829180982138678371) ^ 505496404168711734096910 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3538474829180982138678371) ^ 3150912581639342955190 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3538474829180982138678371) ^ 3748305054852470 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3538474829180982138678371) ^ 74209409920310 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_7155050562388030810855517 : Nat.Prime 7155050562388030810855517 := by
  apply lucas_primality 7155050562388030810855517 (3 : ZMod 7155050562388030810855517)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (113, 1), (179, 1), (1811166823, 1), (3755946823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (113, 1), (179, 1), (1811166823, 1), (3755946823, 1)] : List FactorBlock).map factorBlockValue).prod) = 7155050562388030810855517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_113
      · exact prime_t64_179
      · exact prime_seventeenO_1811166823
      · exact prime_seventeenO_3755946823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7155050562388030810855517) ^ 3577525281194015405427758 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7155050562388030810855517) ^ 550388504799079293142732 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7155050562388030810855517) ^ 63319031525557794786332 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7155050562388030810855517) ^ 39972349510547658161204 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7155050562388030810855517) ^ 3950519892218692 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7155050562388030810855517) ^ 1904992509098692 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_31453109592719841232696631 : Nat.Prime 31453109592719841232696631 := by
  apply lucas_primality 31453109592719841232696631 (11 : ZMod 31453109592719841232696631)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (449330137038854874752809, 1)] : List FactorBlock).map factorBlockValue).prod) = 31453109592719841232696631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_seventeenO_449330137038854874752809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31453109592719841232696631) ^ 15726554796359920616348315 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 6290621918543968246539326 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 4493301370388548747528090 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (11 : ZMod 31453109592719841232696631) ^ 70 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_157019820544906082403852713 : Nat.Prime 157019820544906082403852713 := by
  apply lucas_primality 157019820544906082403852713 (3 : ZMod 157019820544906082403852713)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (22259, 1), (867724171, 1), (1016195213701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (22259, 1), (867724171, 1), (1016195213701, 1)] : List FactorBlock).map factorBlockValue).prod) = 157019820544906082403852713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_seventeenO_22259
      · exact prime_seventeenO_867724171
      · exact prime_seventeenO_1016195213701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 157019820544906082403852713) ^ 78509910272453041201926356 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 157019820544906082403852713) ^ 7054217195062944534968 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 157019820544906082403852713) ^ 180955914094164472 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (3 : ZMod 157019820544906082403852713) ^ 154517378578312 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_205087112548448760690746401 : Nat.Prime 205087112548448760690746401 := by
  apply lucas_primality 205087112548448760690746401 (67 : ZMod 205087112548448760690746401)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 205087112548448760690746401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 205087112548448760690746401) ^ 102543556274224380345373200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 68362370849482920230248800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 41017422509689752138149280 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 18644282958949887335522400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 15775931734496058514672800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 12063947796967574158279200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 10794058555181513720565600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 8916830980367337421336800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 7071969398222371058301600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 6615713308014476151314400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 5542894933741858397047200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 5002124696303628309530400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 4769467733684854899784800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 4363555586137207674271200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 3869568161291486050768800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 3476052755058453571029600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 205087112548448760690746401) ^ 3362083812269651814602400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_257673551663435622406322401 : Nat.Prime 257673551663435622406322401 := by
  apply lucas_primality 257673551663435622406322401 (73 : ZMod 257673551663435622406322401)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 257673551663435622406322401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 257673551663435622406322401) ^ 128836775831717811203161200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 85891183887811874135440800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 51534710332687124481264480 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 36810507380490803200903200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 23424868333039602036938400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 15157267744907977788607200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 13561765877022927495069600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 11203197898410244452448800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 8885294884946055945045600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 8312050053659213626010400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 6964150044957719524495200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 6284720772278917619666400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 5992408178219433079216800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 5482415992839055795879200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 4861765125725200422760800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 4367348333278569871293600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 257673551663435622406322401) ^ 4224156584646485613218400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_279146347635388590940182601 : Nat.Prime 279146347635388590940182601 := by
  apply lucas_primality 279146347635388590940182601 (113 : ZMod 279146347635388590940182601)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 279146347635388590940182601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 279146347635388590940182601) ^ 139573173817694295470091300 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 93048782545129530313394200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 55829269527077718188036520 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 39878049662198370134311800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 25376940694126235540016600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 21472795971952968533860200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 16420373390316975937657800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 14691913033441504786325400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 12136797723277764823486200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 9625736125358227273799400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 9004720891464148094844600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 7544495882037529484869800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 6808447503302160754638600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 6491775526404385835818200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 5939283992242310445535800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 5266912219535633791324200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 4731294027718450693901400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (113 : ZMod 279146347635388590940182601) ^ 4576169633367026080986600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_410174225096897521381492801 : Nat.Prime 410174225096897521381492801 := by
  apply lucas_primality 410174225096897521381492801 (14 : ZMod 410174225096897521381492801)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 410174225096897521381492801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 410174225096897521381492801) ^ 205087112548448760690746400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 136724741698965840460497600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 82034845019379504276298560 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 37288565917899774671044800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 31551863468992117029345600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 24127895593935148316558400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 21588117110363027441131200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 17833661960734674842673600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 14143938796444742116603200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 13231426616028952302628800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 11085789867483716794094400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 10004249392607256619060800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 9538935467369709799569600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 8727111172274415348542400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 7739136322582972101537600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 6952105510116907142059200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (14 : ZMod 410174225096897521381492801) ^ 6724167624539303629204800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_490208220237755574333979201 : Nat.Prime 490208220237755574333979201 := by
  apply lucas_primality 490208220237755574333979201 (67 : ZMod 490208220237755574333979201)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 490208220237755574333979201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (67 : ZMod 490208220237755574333979201) ^ 245104110118877787166989600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 163402740079251858111326400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 98041644047551114866795840 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 70029745748250796333425600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 44564383657977779484907200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 37708324633673505717998400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 28835777661044445549057600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 25800432644092398649156800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 21313400879902416275390400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 16903731732336399114964800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 15813168394766308849483200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 13248870817236637144161600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 11400191168319897077534400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 10429962132718203709233600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 9249211702599161779886400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 8308613902334840242948800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (67 : ZMod 490208220237755574333979201) ^ 8036200331766484825147200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_543203703506702122910625601 : Nat.Prime 543203703506702122910625601 := by
  apply lucas_primality 543203703506702122910625601 (71 : ZMod 543203703506702122910625601)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 543203703506702122910625601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 543203703506702122910625601) ^ 271601851753351061455312800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 181067901168900707636875200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 108640740701340424582125120 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 77600529072386017558660800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 49382154864245647537329600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 41784900269746317146971200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 31953159029806007230036800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 28589668605615901205822400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 23617552326378353170027200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 18731162189886280100366400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 17522700113119423319697600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 13248870817236637144161600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 12632644267597723788619200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 11557525606525577083204800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 10249126481258530620955200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 9206842432316985134078400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (71 : ZMod 543203703506702122910625601) ^ 8904978746011510211649600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_648339904185418662828811201 : Nat.Prime 648339904185418662828811201 := by
  apply lucas_primality 648339904185418662828811201 (73 : ZMod 648339904185418662828811201)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 648339904185418662828811201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 648339904185418662828811201) ^ 324169952092709331414405600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 216113301395139554276270400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 129667980837083732565762240 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 92619986312202666118401600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 58939991289583514802619200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 49872300321955281756062400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 38137641422671686048753600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 34123152851864140148884800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 28188691486322550557774400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 22356548420186850442372800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 17522700113119423319697600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15813168394766308849483200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 15077672190358573554158400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 13794466046498269421889600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 12232828380856955902430400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10988811935346079030996800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (73 : ZMod 648339904185418662828811201) ^ 10628523019433092833259200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1546041309980613734437934401 : Nat.Prime 1546041309980613734437934401 := by
  apply lucas_primality 1546041309980613734437934401 (26 : ZMod 1546041309980613734437934401)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546041309980613734437934401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1546041309980613734437934401) ^ 773020654990306867218967200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 515347103326871244812644800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 309208261996122746887586880 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 220863044282944819205419200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 140549209998237612221630400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 90943606469447866731643200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 81370595262137564970417600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 67219187390461466714692800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 53311769309676335670273600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 49872300321955281756062400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 41784900269746317146971200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 37708324633673505717998400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 35954449069316598475300800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 32894495957034334775275200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 29170590754351202536564800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 26204089999671419227761600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (26 : ZMod 1546041309980613734437934401) ^ 25344939507878913679310400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_1674878085812331545641095601 : Nat.Prime 1674878085812331545641095601 := by
  apply lucas_primality 1674878085812331545641095601 (107 : ZMod 1674878085812331545641095601)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674878085812331545641095601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 1674878085812331545641095601) ^ 837439042906165772820547800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 558292695270777181880365200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 334975617162466309128219120 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 239268297973190220805870800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 152261644164757413240099600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 128836775831717811203161200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 98522240341901855625946800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 88151478200649028717952400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 72820786339666588940917200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 57754416752149363642796400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 54028325348784888569067600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 45266975292225176909218800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 40850685019812964527831600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 38950653158426315014909200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 35635703953453862673214800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 31601473317213802747945200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 28387764166310704163408400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (107 : ZMod 1674878085812331545641095601) ^ 27457017800202156485919600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_10049268514873989273846573601 : Nat.Prime 10049268514873989273846573601 := by
  apply lucas_primality 10049268514873989273846573601 (103 : ZMod 10049268514873989273846573601)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 10049268514873989273846573601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 10049268514873989273846573601) ^ 5024634257436994636923286800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 3349756171624663091282191200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 2009853702974797854769314720 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 1435609787839141324835224800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 913569864988544479440597600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 773020654990306867218967200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 591133442051411133755680800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 528908869203894172307714400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 436924718037999533645503200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 346526500512896181856778400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 324169952092709331414405600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 271601851753351061455312800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 245104110118877787166989600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 233703918950557890089455200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 213814223720723176039288800 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 189608839903282816487671200 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 170326584997864224980450400 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (103 : ZMod 10049268514873989273846573601) ^ 164742106801212938915517600 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem prime_seventeenO_20098537029747978547693147297 : Nat.Prime 20098537029747978547693147297 := by
  apply lucas_primality 20098537029747978547693147297 (7 : ZMod 20098537029747978547693147297)
  · rw [← seventeenOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (223, 1), (10597, 1), (88594225511214335221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (223, 1), (10597, 1), (88594225511214335221, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_223
      · exact prime_seventeenO_10597
      · exact prime_seventeenO_88594225511214335221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20098537029747978547693147297) ^ 10049268514873989273846573648 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20098537029747978547693147297) ^ 6699512343249326182564382432 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20098537029747978547693147297) ^ 90127968743264477792345952 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20098537029747978547693147297) ^ 1896625179744076488411168 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide
    · change (7 : ZMod 20098537029747978547693147297) ^ 226860576 ≠ 1
      rw [← seventeenOFastPow_eq_pow]
      decide

private theorem phi_seventeenO_20098537029747978547693147200 : Nat.totient 20098537029747978547693147200 = 2644713263809130869555200000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 2), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147201 : Nat.totient 20098537029747978547693147201 = 20089694715434961712395596160 := by
  rw [← show ((([(2273, 1), (1052072531, 1), (8404644125874427, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_2273, prime_seventeenO_1052072531, prime_seventeenO_8404644125874427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147202 : Nat.totient 20098537029747978547693147202 = 10049268514873989273846573600 := by
  rw [← show ((([(2, 1), (10049268514873989273846573601, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_10049268514873989273846573601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147203 : Nat.totient 20098537029747978547693147203 = 13394834325010510836904177920 := by
  rw [← show ((([(3, 1), (3863, 1), (19891, 1), (299027, 1), (3960137, 1), (73627703, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_seventeenO_3863, prime_seventeenO_19891, prime_seventeenO_299027, prime_seventeenO_3960137, prime_seventeenO_73627703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147204 : Nat.totient 20098537029747978547693147204 = 10049268514669542641667799008 := by
  rw [← show ((([(2, 2), (49153528429, 1), (102223266935858869, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_49153528429, prime_seventeenO_102223266935858869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147205 : Nat.totient 20098537029747978547693147205 = 15875299685995237821163364352 := by
  rw [← show ((([(5, 1), (79, 1), (52142977, 1), (111306893, 1), (8766968939, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_79, prime_seventeenO_52142977, prime_seventeenO_111306893, prime_seventeenO_8766968939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147206 : Nat.totient 20098537029747978547693147206 = 6684245771450603771322208704 := by
  rw [← show ((([(2, 1), (3, 1), (439, 1), (1167833, 1), (6533831533403812223, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_439, prime_seventeenO_1167833, prime_seventeenO_6533831533403812223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147207 : Nat.totient 20098537029747978547693147207 = 17226778612256449479044952192 := by
  rw [← show ((([(7, 1), (54833, 1), (76679, 1), (682885605572149543, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_seventeenO_54833, prime_seventeenO_76679, prime_seventeenO_682885605572149543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147208 : Nat.totient 20098537029747978547693147208 = 10046916331206419479149158400 := by
  rw [← show ((([(2, 3), (4801, 1), (40163, 1), (1133689, 1), (11492716013243, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_4801, prime_seventeenO_40163, prime_seventeenO_1133689, prime_seventeenO_11492716013243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147209 : Nat.totient 20098537029747978547693147209 = 13210306028942333317732584600 := by
  rw [← show ((([(3, 2), (71, 1), (31453109592719841232696631, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_71, prime_seventeenO_31453109592719841232696631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147210 : Nat.totient 20098537029747978547693147210 = 8039319674273167500501023248 := by
  rw [← show ((([(2, 1), (5, 1), (84503, 1), (23784406505979643974407, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_seventeenO_84503, prime_seventeenO_23784406505979643974407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147211 : Nat.totient 20098537029747978547693147211 = 18270914529741567029834935720 := by
  rw [← show ((([(11, 1), (37847, 1), (48277002932255897663783, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_seventeenO_37847, prime_seventeenO_48277002932255897663783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147212 : Nat.totient 20098537029747978547693147212 = 6699512343249326182564382400 := by
  rw [← show ((([(2, 2), (3, 1), (1674878085812331545641095601, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_seventeenO_1674878085812331545641095601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147213 : Nat.totient 20098537029747978547693147213 = 18552495719767364813255212800 := by
  rw [← show ((([(13, 1), (1546041309980613734437934401, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_seventeenO_1546041309980613734437934401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147214 : Nat.totient 20098537029747978547693147214 = 8612690113418257212948306432 := by
  rw [← show ((([(2, 1), (7, 1), (8893, 1), (344755493, 1), (468249070338449, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_seventeenO_8893, prime_seventeenO_344755493, prime_seventeenO_468249070338449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147215 : Nat.totient 20098537029747978547693147215 = 10695260366395870073208035328 := by
  rw [← show ((([(3, 1), (5, 1), (743, 1), (1123, 1), (88685873, 1), (18107153021773, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_seventeenO_743, prime_seventeenO_1123, prime_seventeenO_88685873, prime_seventeenO_18107153021773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147216 : Nat.totient 20098537029747978547693147216 = 10043766665920248159900672000 := by
  rw [← show ((([(2, 4), (2693, 1), (5701, 1), (1231261, 1), (66451830061937, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_2693, prime_seventeenO_5701, prime_seventeenO_1231261, prime_seventeenO_66451830061937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147217 : Nat.totient 20098537029747978547693147217 = 18728877245652730232015619072 := by
  rw [← show ((([(17, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147218 : Nat.totient 20098537029747978547693147218 = 6681582454611170234976933888 := by
  rw [← show ((([(2, 1), (3, 2), (397, 1), (6337, 1), (443831096543292924709, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_seventeenO_397, prime_seventeenO_6337, prime_seventeenO_443831096543292924709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147219 : Nat.totient 20098537029747978547693147219 = 18859385520008252838548213760 := by
  rw [← show ((([(19, 1), (109, 1), (2857, 1), (439441, 1), (9978323, 1), (774668639, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_t64_109, prime_seventeenO_2857, prime_seventeenO_439441, prime_seventeenO_9978323, prime_seventeenO_774668639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147220 : Nat.totient 20098537029747978547693147220 = 8027286842036676498917068800 := by
  rw [← show ((([(2, 2), (5, 1), (887, 1), (3637, 1), (11317, 1), (54601, 1), (504121961207, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_seventeenO_887, prime_seventeenO_3637, prime_seventeenO_11317, prime_seventeenO_54601, prime_seventeenO_504121961207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147221 : Nat.totient 20098537029747978547693147221 = 11484878296664508317990826048 := by
  rw [← show ((([(3, 1), (7, 1), (1898759389, 1), (504051854825488309, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_seventeenO_1898759389, prime_seventeenO_504051854825488309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147222 : Nat.totient 20098537029747978547693147222 = 9135406951481478798351160800 := by
  rw [← show ((([(2, 1), (11, 1), (31319, 1), (111179436971, 1), (262367120149, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_seventeenO_31319, prime_seventeenO_111179436971, prime_seventeenO_262367120149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147223 : Nat.totient 20098537029747978547693147223 = 19224628848785001450671765760 := by
  rw [← show ((([(23, 1), (327263, 1), (21764550497, 1), (122684585791, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_seventeenO_327263, prime_seventeenO_21764550497, prime_seventeenO_122684585791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147224 : Nat.totient 20098537029747978547693147224 = 6685755644392551385474923936 := by
  rw [← show ((([(2, 3), (3, 1), (487, 1), (1719587357096849636181823, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_seventeenO_487, prime_seventeenO_1719587357096849636181823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147225 : Nat.totient 20098537029747978547693147225 = 15949740735921967321248276480 := by
  rw [← show ((([(5, 2), (197, 1), (337, 1), (16046729, 1), (754643424782869, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_197, prime_seventeenO_337, prime_seventeenO_16046729, prime_seventeenO_754643424782869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147226 : Nat.totient 20098537029747978547693147226 = 9276245549836413457207127040 := by
  rw [← show ((([(2, 1), (13, 1), (4930417, 1), (21642461, 1), (7244372988773, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_seventeenO_4930417, prime_seventeenO_21642461, prime_seventeenO_7244372988773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147227 : Nat.totient 20098537029747978547693147227 = 13399012235293974285535623168 := by
  rw [← show ((([(3, 6), (1076753, 1), (2179651489, 1), (11747183939, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_seventeenO_1076753, prime_seventeenO_2179651489, prime_seventeenO_11747183939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147228 : Nat.totient 20098537029747978547693147228 = 8613658625905677303688680000 := by
  rw [← show ((([(2, 2), (7, 1), (122594851, 1), (282861461, 1), (20699526191, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_seventeenO_122594851, prime_seventeenO_282861461, prime_seventeenO_20699526191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147229 : Nat.totient 20098537029747978547693147229 = 19288195945570901143322465280 := by
  rw [← show ((([(29, 1), (167, 1), (19421, 1), (223283, 1), (2432869, 1), (393372509, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_t64_167, prime_seventeenO_19421, prime_seventeenO_223283, prime_seventeenO_2432869, prime_seventeenO_393372509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147230 : Nat.totient 20098537029747978547693147230 = 5336199300225407111299718016 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (229, 1), (865643, 1), (3379627908495294503, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_229, prime_seventeenO_865643, prime_seventeenO_3379627908495294503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147231 : Nat.totient 20098537029747978547693147231 = 19450197125562559884864336000 := by
  rw [← show ((([(31, 1), (648339904185418662828811201, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_seventeenO_648339904185418662828811201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147232 : Nat.totient 20098537029747978547693147232 = 10049267138998616938999188864 := by
  rw [← show ((([(2, 5), (7303909, 1), (85992210770920657639, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_7303909, prime_seventeenO_85992210770920657639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147233 : Nat.totient 20098537029747978547693147233 = 12180927946332795642063936080 := by
  rw [← show ((([(3, 1), (11, 1), (3395999, 1), (179342389870853805599, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_seventeenO_3395999, prime_seventeenO_179342389870853805599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147234 : Nat.totient 20098537029747978547693147234 = 9458135065086595926115297600 := by
  rw [← show ((([(2, 1), (17, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147235 : Nat.totient 20098537029747978547693147235 = 13781780839498172047098812928 := by
  rw [← show ((([(5, 1), (7, 1), (188473, 1), (3046823232694638117577, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_seventeenO_188473, prime_seventeenO_3046823232694638117577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147236 : Nat.totient 20098537029747978547693147236 = 6691273778037450469338551808 := by
  rw [← show ((([(2, 2), (3, 2), (1373, 1), (1993, 1), (304357847, 1), (670346901547, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_1373, prime_seventeenO_1993, prime_seventeenO_304357847, prime_seventeenO_670346901547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147237 : Nat.totient 20098537029747978547693147237 = 19555333326241276424782521600 := by
  rw [← show ((([(37, 1), (543203703506702122910625601, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_seventeenO_543203703506702122910625601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147238 : Nat.totient 20098537029747978547693147238 = 9520353514441488455107993440 := by
  rw [← show ((([(2, 1), (19, 1), (1553471, 1), (3544788469, 1), (96047789699, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_seventeenO_1553471, prime_seventeenO_3544788469, prime_seventeenO_96047789699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147239 : Nat.totient 20098537029747978547693147239 = 12368314273048038661685278848 := by
  rw [← show ((([(3, 1), (13, 1), (763157, 1), (675283202967241661693, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_seventeenO_763157, prime_seventeenO_675283202967241661693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147240 : Nat.totient 20098537029747978547693147240 = 8039414654040781988151515200 := by
  rw [← show ((([(2, 3), (5, 1), (50928011, 1), (9866150589381930971, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_seventeenO_50928011, prime_seventeenO_9866150589381930971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147241 : Nat.totient 20098537029747978547693147241 = 19608328809510222973359168000 := by
  rw [← show ((([(41, 1), (490208220237755574333979201, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_seventeenO_490208220237755574333979201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147242 : Nat.totient 20098537029747978547693147242 = 5742438969158677124220680064 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (32896043, 1), (783928043, 1), (18556467049, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_seventeenO_32896043, prime_seventeenO_783928043, prime_seventeenO_18556467049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147243 : Nat.totient 20098537029747978547693147243 = 19337589101082039294100809600 := by
  rw [← show ((([(43, 1), (67, 1), (36923, 1), (1340981, 1), (140896947156781, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_67, prime_seventeenO_36923, prime_seventeenO_1340981, prime_seventeenO_140896947156781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147244 : Nat.totient 20098537029747978547693147244 = 9135698648354517615513986240 := by
  rw [← show ((([(2, 2), (11, 1), (5967429077, 1), (76546352977170413, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_seventeenO_5967429077, prime_seventeenO_76546352977170413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147245 : Nat.totient 20098537029747978547693147245 = 10718262419579452487629035648 := by
  rw [← show ((([(3, 2), (5, 1), (11197, 1), (39888734144558519737813, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_seventeenO_11197, prime_seventeenO_39888734144558519737813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147246 : Nat.totient 20098537029747978547693147246 = 9612343793578951209680150200 := by
  rw [← show ((([(2, 1), (23, 1), (2951252771, 1), (148047202981516331, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_seventeenO_2951252771, prime_seventeenO_148047202981516331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147247 : Nat.totient 20098537029747978547693147247 = 19567772141038379424239454720 := by
  rw [← show ((([(47, 1), (193, 1), (16111, 1), (137526623891778748687, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_193, prime_seventeenO_16111, prime_seventeenO_137526623891778748687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147248 : Nat.totient 20098537029747978547693147248 = 6636900077442176725273529088 := by
  rw [← show ((([(2, 4), (3, 1), (107, 1), (7237965619, 1), (540658350927197, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_107, prime_seventeenO_7237965619, prime_seventeenO_540658350927197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147249 : Nat.totient 20098537029747978547693147249 = 17227317454069695898022697600 := by
  rw [← show ((([(7, 2), (410174225096897521381492801, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_seventeenO_410174225096897521381492801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147250 : Nat.totient 20098537029747978547693147250 = 8039390274352894095149875200 := by
  rw [← show ((([(2, 1), (5, 3), (327829, 1), (560942329, 1), (437178560129, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_seventeenO_327829, prime_seventeenO_560942329, prime_seventeenO_437178560129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147251 : Nat.totient 20098537029747978547693147251 = 12610846763763437520121190400 := by
  rw [← show ((([(3, 1), (17, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147252 : Nat.totient 20098537029747978547693147252 = 9155012532968977752013148160 := by
  rw [← show ((([(2, 2), (13, 1), (97, 1), (359, 1), (293827, 1), (37774890916250381, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_97, prime_seventeenO_359, prime_seventeenO_293827, prime_seventeenO_37774890916250381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147253 : Nat.totient 20098537029747978547693147253 = 19719319349941412914717802096 := by
  rw [← show ((([(53, 2), (7155050562388030810855517, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_seventeenO_7155050562388030810855517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147254 : Nat.totient 20098537029747978547693147254 = 6568660020554065621553974272 := by
  rw [← show ((([(2, 1), (3, 3), (73, 1), (173, 1), (10837, 1), (23719, 1), (114655864909423, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_73, prime_seventeenO_173, prime_seventeenO_10837, prime_seventeenO_23719, prime_seventeenO_114655864909423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147255 : Nat.totient 20098537029747978547693147255 = 14600774884282283879497728000 := by
  rw [← show ((([(5, 1), (11, 1), (971, 1), (12289, 1), (144479, 1), (211963584708541, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_seventeenO_971, prime_seventeenO_12289, prime_seventeenO_144479, prime_seventeenO_211963584708541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147256 : Nat.totient 20098537029747978547693147256 = 8604842290216733595123947520 := by
  rw [← show ((([(2, 3), (7, 1), (977, 1), (213499073093, 1), (1720623545941, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_seventeenO_977, prime_seventeenO_213499073093, prime_seventeenO_1720623545941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147257 : Nat.totient 20098537029747978547693147257 = 12692072900682230079599308800 := by
  rw [← show ((([(3, 1), (19, 2), (7297, 1), (34598807, 1), (73507308180701, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_seventeenO_7297, prime_seventeenO_34598807, prime_seventeenO_73507308180701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147258 : Nat.totient 20098537029747978547693147258 = 9692880688540687630971686400 := by
  rw [← show ((([(2, 1), (29, 1), (1321, 1), (3853, 1), (2752604287, 1), (24733799971, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_seventeenO_1321, prime_seventeenO_3853, prime_seventeenO_2752604287, prime_seventeenO_24733799971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147259 : Nat.totient 20098537029747978547693147259 = 19757883859690331199749865856 := by
  rw [← show ((([(59, 1), (319188383753, 1), (1067248018209017, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_seventeenO_319188383753, prime_seventeenO_1067248018209017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147260 : Nat.totient 20098537029747978547693147260 = 5353540101242043662986880832 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (883, 1), (379360834838580191538187, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_883, prime_seventeenO_379360834838580191538187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147261 : Nat.totient 20098537029747978547693147261 = 19643135282284752971327949120 := by
  rw [← show ((([(61, 1), (157, 1), (2098625564346661642235893, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_t64_157, prime_seventeenO_2098625564346661642235893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147262 : Nat.totient 20098537029747978547693147262 = 9694027889486156300480098560 := by
  rw [← show ((([(2, 1), (31, 1), (313, 1), (136808989, 1), (7570312122546493, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_seventeenO_313, prime_seventeenO_136808989, prime_seventeenO_7570312122546493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147263 : Nat.totient 20098537029747978547693147263 = 11344620418304032168232394240 := by
  rw [← show ((([(3, 2), (7, 1), (89, 1), (1031, 1), (56747, 1), (61267804512617837, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_89, prime_seventeenO_1031, prime_seventeenO_56747, prime_seventeenO_61267804512617837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147264 : Nat.totient 20098537029747978547693147264 = 10049268514873989273846573568 := by
  rw [← show ((([(2, 7), (157019820544906082403852713, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_seventeenO_157019820544906082403852713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147265 : Nat.totient 20098537029747978547693147265 = 14841408050631270730868279040 := by
  rw [← show ((([(5, 1), (13, 1), (25219, 1), (19276921021, 1), (636041656519, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_seventeenO_25219, prime_seventeenO_19276921021, prime_seventeenO_636041656519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147266 : Nat.totient 20098537029747978547693147266 = 6026315969053514833352300160 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (137, 1), (307, 1), (7240383469162719667139, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_137, prime_t64_307, prime_seventeenO_7240383469162719667139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147267 : Nat.totient 20098537029747978547693147267 = 20029941339948099183807902880 := by
  rw [← show ((([(293, 1), (71911962181, 1), (953884269611099, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_293, prime_seventeenO_71911962181, prime_seventeenO_953884269611099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147268 : Nat.totient 20098537029747978547693147268 = 9458134620944793194601529344 := by
  rw [← show ((([(2, 2), (17, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147269 : Nat.totient 20098537029747978547693147269 = 12576906924866396282656640000 := by
  rw [← show ((([(3, 1), (23, 1), (101, 1), (113, 1), (35051, 1), (728140395727948727, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_t64_101, prime_t64_113, prime_seventeenO_35051, prime_seventeenO_728140395727948727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147270 : Nat.totient 20098537029747978547693147270 = 6866544778159847181913128960 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (449, 1), (761, 1), (840302021920015759849, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_seventeenO_449, prime_t64_761, prime_seventeenO_840302021920015759849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147271 : Nat.totient 20098537029747978547693147271 = 20098388395016466815206581000 := by
  rw [← show ((([(135221, 1), (148634731511732486431051, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_135221, prime_seventeenO_148634731511732486431051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147272 : Nat.totient 20098537029747978547693147272 = 6699512343249326182564382400 := by
  rw [← show ((([(2, 3), (3, 2), (279146347635388590940182601, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_seventeenO_279146347635388590940182601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147273 : Nat.totient 20098537029747978547693147273 = 20075049187279056425997964800 := by
  rw [← show ((([(941, 1), (10181, 1), (152027, 1), (800873, 1), (17230584403, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_941, prime_seventeenO_10181, prime_seventeenO_152027, prime_seventeenO_800873, prime_seventeenO_17230584403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147274 : Nat.totient 20098537029747978547693147274 = 9777658843220671146429703872 := by
  rw [← show ((([(2, 1), (37, 1), (1250357, 1), (217219443529608792893, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_seventeenO_1250357, prime_seventeenO_217219443529608792893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147275 : Nat.totient 20098537029747978547693147275 = 10686835345047850528644931200 := by
  rw [← show ((([(3, 1), (5, 2), (331, 1), (196248589, 1), (4125424526678383, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_seventeenO_331, prime_seventeenO_196248589, prime_seventeenO_4125424526678383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147276 : Nat.totient 20098537029747978547693147276 = 9520352125525917842833713600 := by
  rw [← show ((([(2, 2), (19, 1), (1265981, 1), (208892893812740543621, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_seventeenO_1265981, prime_seventeenO_208892893812740543621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147277 : Nat.totient 20098537029747978547693147277 = 15417827660968798063653705600 := by
  rw [← show ((([(7, 1), (11, 2), (83, 1), (283, 1), (1996949, 1), (505882358351831, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_83, prime_t64_283, prime_seventeenO_1996949, prime_seventeenO_505882358351831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147278 : Nat.totient 20098537029747978547693147278 = 6184165239922454937751737600 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (257673551663435622406322401, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_seventeenO_257673551663435622406322401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147279 : Nat.totient 20098537029747978547693147279 = 20022248162727099743881238976 := by
  rw [← show ((([(499, 1), (557, 1), (72311722294671851954153, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_499, prime_seventeenO_557, prime_seventeenO_72311722294671851954153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147280 : Nat.totient 20098537029747978547693147280 = 7926183617365399990639548800 := by
  rw [← show ((([(2, 4), (5, 1), (71, 1), (3538474829180982138678371, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_71, prime_seventeenO_3538474829180982138678371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147281 : Nat.totient 20098537029747978547693147281 = 13370863147237375271568072000 := by
  rw [← show ((([(3, 3), (523, 1), (5261, 1), (270539505267134450701, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_seventeenO_523, prime_seventeenO_5261, prime_seventeenO_270539505267134450701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147282 : Nat.totient 20098537029747978547693147282 = 9802684246861754810565672960 := by
  rw [← show ((([(2, 1), (41, 1), (6737, 1), (395293, 1), (133252297, 1), (690701213, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_seventeenO_6737, prime_seventeenO_395293, prime_seventeenO_133252297, prime_seventeenO_690701213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147283 : Nat.totient 20098537029747978547693147283 = 19896838429589729548012800000 := by
  rw [← show ((([(151, 1), (577, 1), (587, 1), (528911, 1), (10154951, 1), (73166647, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_151, prime_seventeenO_577, prime_seventeenO_587, prime_seventeenO_528911, prime_seventeenO_10154951, prime_seventeenO_73166647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147284 : Nat.totient 20098537029747978547693147284 = 5663762851627598718119213952 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (79, 1), (947, 1), (42880543, 1), (74584367950139, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_79, prime_seventeenO_947, prime_seventeenO_42880543, prime_seventeenO_74584367950139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147285 : Nat.totient 20098537029747978547693147285 = 15133016092345093309182697728 := by
  rw [← show ((([(5, 1), (17, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147286 : Nat.totient 20098537029747978547693147286 = 9815562273631349524492060200 := by
  rw [← show ((([(2, 1), (43, 1), (4226671, 1), (55292668615692560431, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_seventeenO_4226671, prime_seventeenO_55292668615692560431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147287 : Nat.totient 20098537029747978547693147287 = 12850143184246936875556472832 := by
  rw [← show ((([(3, 1), (29, 1), (149, 1), (619693, 1), (2501971364848882193, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_149, prime_seventeenO_619693, prime_seventeenO_2501971364848882193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147288 : Nat.totient 20098537029747978547693147288 = 9101778284646034543903334400 := by
  rw [← show ((([(2, 3), (11, 1), (277, 1), (9689, 1), (664303721, 1), (128102133877, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_seventeenO_277, prime_seventeenO_9689, prime_seventeenO_664303721, prime_seventeenO_128102133877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147289 : Nat.totient 20098537029747978547693147289 = 20097946660278753949487308416 := by
  rw [← show ((([(36217, 1), (567389, 1), (978072529592328853, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_36217, prime_seventeenO_567389, prime_seventeenO_978072529592328853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147290 : Nat.totient 20098537029747978547693147290 = 5359609873906886359225200768 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7738677413, 1), (28857266712418637, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_seventeenO_7738677413, prime_seventeenO_28857266712418637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147291 : Nat.totient 20098537029747978547693147291 = 15902135725772071277738413344 := by
  rw [← show ((([(7, 1), (13, 1), (4592543, 1), (48091666051454459807, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_seventeenO_4592543, prime_seventeenO_48091666051454459807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147292 : Nat.totient 20098537029747978547693147292 = 9612010018796515076962678848 := by
  rw [← show ((([(2, 2), (23, 1), (30773, 1), (448843, 1), (15816570652505159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_seventeenO_30773, prime_seventeenO_448843, prime_seventeenO_15816570652505159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147293 : Nat.totient 20098537029747978547693147293 = 12966794639890309194979104240 := by
  rw [← show ((([(3, 1), (31, 1), (3765239, 1), (57396967734356186759, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_seventeenO_3765239, prime_seventeenO_57396967734356186759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147294 : Nat.totient 20098537029747978547693147294 = 9835122135728216174936117400 := by
  rw [← show ((([(2, 1), (47, 1), (29611, 1), (7220770109780931952291, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_seventeenO_29611, prime_seventeenO_7220770109780931952291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147295 : Nat.totient 20098537029747978547693147295 = 15231333823618214867180912640 := by
  rw [← show ((([(5, 1), (19, 1), (12269, 1), (255656449, 1), (67448907900581, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_seventeenO_12269, prime_seventeenO_255656449, prime_seventeenO_67448907900581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147296 : Nat.totient 20098537029747978547693147296 = 6668840313623539689920916480 := by
  rw [← show ((([(2, 5), (3, 1), (223, 1), (10597, 1), (88594225511214335221, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_223, prime_seventeenO_10597, prime_seventeenO_88594225511214335221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147297 : Nat.totient 20098537029747978547693147297 = 20098537029747978547693147296 := by
  rw [← show ((([(20098537029747978547693147297, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventeenO_20098537029747978547693147297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147298 : Nat.totient 20098537029747978547693147298 = 8613658727034847949011348800 := by
  rw [← show ((([(2, 1), (7, 2), (205087112548448760690746401, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_seventeenO_205087112548448760690746401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventeenO_20098537029747978547693147299 : Nat.totient 20098537029747978547693147299 = 12180327709677238050380147520 := by
  rw [← show ((([(3, 2), (11, 1), (20173, 1), (10063725055916813776837, 1)] : List FactorBlock).map factorBlockValue).prod) = 20098537029747978547693147299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_seventeenO_20173, prime_seventeenO_10063725055916813776837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventeenO : certifiedKill 1 20098537029747978547693147199 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventeenO_20098537029747978547693147200, phi_seventeenO_20098537029747978547693147201, phi_seventeenO_20098537029747978547693147202,
    phi_seventeenO_20098537029747978547693147203, phi_seventeenO_20098537029747978547693147204, phi_seventeenO_20098537029747978547693147205,
    phi_seventeenO_20098537029747978547693147206, phi_seventeenO_20098537029747978547693147207, phi_seventeenO_20098537029747978547693147208,
    phi_seventeenO_20098537029747978547693147209, phi_seventeenO_20098537029747978547693147210, phi_seventeenO_20098537029747978547693147211,
    phi_seventeenO_20098537029747978547693147212, phi_seventeenO_20098537029747978547693147213, phi_seventeenO_20098537029747978547693147214,
    phi_seventeenO_20098537029747978547693147215, phi_seventeenO_20098537029747978547693147216, phi_seventeenO_20098537029747978547693147217,
    phi_seventeenO_20098537029747978547693147218, phi_seventeenO_20098537029747978547693147219, phi_seventeenO_20098537029747978547693147220,
    phi_seventeenO_20098537029747978547693147221, phi_seventeenO_20098537029747978547693147222, phi_seventeenO_20098537029747978547693147223,
    phi_seventeenO_20098537029747978547693147224, phi_seventeenO_20098537029747978547693147225, phi_seventeenO_20098537029747978547693147226,
    phi_seventeenO_20098537029747978547693147227, phi_seventeenO_20098537029747978547693147228, phi_seventeenO_20098537029747978547693147229,
    phi_seventeenO_20098537029747978547693147230, phi_seventeenO_20098537029747978547693147231, phi_seventeenO_20098537029747978547693147232,
    phi_seventeenO_20098537029747978547693147233, phi_seventeenO_20098537029747978547693147234, phi_seventeenO_20098537029747978547693147235,
    phi_seventeenO_20098537029747978547693147236, phi_seventeenO_20098537029747978547693147237, phi_seventeenO_20098537029747978547693147238,
    phi_seventeenO_20098537029747978547693147239, phi_seventeenO_20098537029747978547693147240, phi_seventeenO_20098537029747978547693147241,
    phi_seventeenO_20098537029747978547693147242, phi_seventeenO_20098537029747978547693147243, phi_seventeenO_20098537029747978547693147244,
    phi_seventeenO_20098537029747978547693147245, phi_seventeenO_20098537029747978547693147246, phi_seventeenO_20098537029747978547693147247,
    phi_seventeenO_20098537029747978547693147248, phi_seventeenO_20098537029747978547693147249, phi_seventeenO_20098537029747978547693147250,
    phi_seventeenO_20098537029747978547693147251, phi_seventeenO_20098537029747978547693147252, phi_seventeenO_20098537029747978547693147253,
    phi_seventeenO_20098537029747978547693147254, phi_seventeenO_20098537029747978547693147255, phi_seventeenO_20098537029747978547693147256,
    phi_seventeenO_20098537029747978547693147257, phi_seventeenO_20098537029747978547693147258, phi_seventeenO_20098537029747978547693147259,
    phi_seventeenO_20098537029747978547693147260, phi_seventeenO_20098537029747978547693147261, phi_seventeenO_20098537029747978547693147262,
    phi_seventeenO_20098537029747978547693147263, phi_seventeenO_20098537029747978547693147264, phi_seventeenO_20098537029747978547693147265,
    phi_seventeenO_20098537029747978547693147266, phi_seventeenO_20098537029747978547693147267, phi_seventeenO_20098537029747978547693147268,
    phi_seventeenO_20098537029747978547693147269, phi_seventeenO_20098537029747978547693147270, phi_seventeenO_20098537029747978547693147271,
    phi_seventeenO_20098537029747978547693147272, phi_seventeenO_20098537029747978547693147273, phi_seventeenO_20098537029747978547693147274,
    phi_seventeenO_20098537029747978547693147275, phi_seventeenO_20098537029747978547693147276, phi_seventeenO_20098537029747978547693147277,
    phi_seventeenO_20098537029747978547693147278, phi_seventeenO_20098537029747978547693147279, phi_seventeenO_20098537029747978547693147280,
    phi_seventeenO_20098537029747978547693147281, phi_seventeenO_20098537029747978547693147282, phi_seventeenO_20098537029747978547693147283,
    phi_seventeenO_20098537029747978547693147284, phi_seventeenO_20098537029747978547693147285, phi_seventeenO_20098537029747978547693147286,
    phi_seventeenO_20098537029747978547693147287, phi_seventeenO_20098537029747978547693147288, phi_seventeenO_20098537029747978547693147289,
    phi_seventeenO_20098537029747978547693147290, phi_seventeenO_20098537029747978547693147291, phi_seventeenO_20098537029747978547693147292,
    phi_seventeenO_20098537029747978547693147293, phi_seventeenO_20098537029747978547693147294, phi_seventeenO_20098537029747978547693147295,
    phi_seventeenO_20098537029747978547693147296, phi_seventeenO_20098537029747978547693147297, phi_seventeenO_20098537029747978547693147298,
    phi_seventeenO_20098537029747978547693147299]

end TotientTailPeriodKiller
end Erdos249257
