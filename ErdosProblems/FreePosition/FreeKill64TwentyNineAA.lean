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
  prime_t64_167
  prime_t64_179
  prime_t64_191
  prime_t64_193
  prime_t64_197
  prime_t64_227
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_307
  prime_t64_311
  prime_t64_317
  prime_t64_349
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_433
  prime_t64_439
  prime_t64_461
  prime_t64_467
  prime_t64_479
  prime_t64_491
  prime_t64_617
  prime_t64_647
  prime_t64_661
  prime_t64_673
  prime_t64_719
  prime_t64_761
  prime_t64_787
  prime_t64_997
  prime_t64_1093
  prime_t64_1789
  prime_t64_3739
  prime_t64_5009
  from Erdos249257.DiagonalPincerCertificatesT64

private def twentyNineAAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyNineAAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyNineAAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyNineAAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyNineAAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyNineAAFastPow a n * twentyNineAAFastPow a n * a
        else twentyNineAAFastPow a n * twentyNineAAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyNineAA_127 : Nat.Prime 127 := by norm_num

private theorem prime_twentyNineAA_131 : Nat.Prime 131 := by norm_num

private theorem prime_twentyNineAA_151 : Nat.Prime 151 := by norm_num

private theorem prime_twentyNineAA_173 : Nat.Prime 173 := by norm_num

private theorem prime_twentyNineAA_181 : Nat.Prime 181 := by norm_num

private theorem prime_twentyNineAA_241 : Nat.Prime 241 := by norm_num

private theorem prime_twentyNineAA_257 : Nat.Prime 257 := by norm_num

private theorem prime_twentyNineAA_277 : Nat.Prime 277 := by norm_num

private theorem prime_twentyNineAA_281 : Nat.Prime 281 := by norm_num

private theorem prime_twentyNineAA_293 : Nat.Prime 293 := by norm_num

private theorem prime_twentyNineAA_313 : Nat.Prime 313 := by norm_num

private theorem prime_twentyNineAA_331 : Nat.Prime 331 := by norm_num

private theorem prime_twentyNineAA_337 : Nat.Prime 337 := by norm_num

private theorem prime_twentyNineAA_347 : Nat.Prime 347 := by norm_num

private theorem prime_twentyNineAA_353 : Nat.Prime 353 := by norm_num

private theorem prime_twentyNineAA_367 : Nat.Prime 367 := by norm_num

private theorem prime_twentyNineAA_373 : Nat.Prime 373 := by norm_num

private theorem prime_twentyNineAA_379 : Nat.Prime 379 := by norm_num

private theorem prime_twentyNineAA_397 : Nat.Prime 397 := by norm_num

private theorem prime_twentyNineAA_419 : Nat.Prime 419 := by norm_num

private theorem prime_twentyNineAA_443 : Nat.Prime 443 := by norm_num

private theorem prime_twentyNineAA_449 : Nat.Prime 449 := by norm_num

private theorem prime_twentyNineAA_463 : Nat.Prime 463 := by norm_num

private theorem prime_twentyNineAA_487 : Nat.Prime 487 := by norm_num

private theorem prime_twentyNineAA_509 : Nat.Prime 509 := by norm_num

private theorem prime_twentyNineAA_541 : Nat.Prime 541 := by norm_num

private theorem prime_twentyNineAA_547 : Nat.Prime 547 := by norm_num

private theorem prime_twentyNineAA_571 : Nat.Prime 571 := by norm_num

private theorem prime_twentyNineAA_587 : Nat.Prime 587 := by norm_num

private theorem prime_twentyNineAA_619 : Nat.Prime 619 := by norm_num

private theorem prime_twentyNineAA_727 : Nat.Prime 727 := by norm_num

private theorem prime_twentyNineAA_733 : Nat.Prime 733 := by norm_num

private theorem prime_twentyNineAA_739 : Nat.Prime 739 := by norm_num

private theorem prime_twentyNineAA_743 : Nat.Prime 743 := by norm_num

private theorem prime_twentyNineAA_757 : Nat.Prime 757 := by norm_num

private theorem prime_twentyNineAA_809 : Nat.Prime 809 := by norm_num

private theorem prime_twentyNineAA_811 : Nat.Prime 811 := by norm_num

private theorem prime_twentyNineAA_829 : Nat.Prime 829 := by norm_num

private theorem prime_twentyNineAA_857 : Nat.Prime 857 := by norm_num

private theorem prime_twentyNineAA_863 : Nat.Prime 863 := by norm_num

private theorem prime_twentyNineAA_907 : Nat.Prime 907 := by norm_num

private theorem prime_twentyNineAA_941 : Nat.Prime 941 := by norm_num

private theorem prime_twentyNineAA_967 : Nat.Prime 967 := by norm_num

private theorem prime_twentyNineAA_971 : Nat.Prime 971 := by norm_num

private theorem prime_twentyNineAA_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_twentyNineAA_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_twentyNineAA_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_twentyNineAA_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_twentyNineAA_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_twentyNineAA_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_twentyNineAA_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_twentyNineAA_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_twentyNineAA_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_twentyNineAA_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_twentyNineAA_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_twentyNineAA_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_twentyNineAA_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_twentyNineAA_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_twentyNineAA_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_twentyNineAA_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_twentyNineAA_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_twentyNineAA_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_twentyNineAA_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_twentyNineAA_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_twentyNineAA_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_twentyNineAA_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_twentyNineAA_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_twentyNineAA_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_twentyNineAA_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_twentyNineAA_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_twentyNineAA_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_twentyNineAA_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_twentyNineAA_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_twentyNineAA_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_twentyNineAA_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_twentyNineAA_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_twentyNineAA_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_twentyNineAA_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_twentyNineAA_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_twentyNineAA_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_twentyNineAA_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_twentyNineAA_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_twentyNineAA_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_twentyNineAA_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_twentyNineAA_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_twentyNineAA_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_twentyNineAA_3301 : Nat.Prime 3301 := by norm_num

private theorem prime_twentyNineAA_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_twentyNineAA_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_twentyNineAA_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_twentyNineAA_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_twentyNineAA_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_twentyNineAA_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_twentyNineAA_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_twentyNineAA_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_twentyNineAA_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_twentyNineAA_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_twentyNineAA_4547 : Nat.Prime 4547 := by norm_num

private theorem prime_twentyNineAA_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_twentyNineAA_4799 : Nat.Prime 4799 := by norm_num

private theorem prime_twentyNineAA_5297 : Nat.Prime 5297 := by norm_num

private theorem prime_twentyNineAA_5413 : Nat.Prime 5413 := by norm_num

private theorem prime_twentyNineAA_5437 : Nat.Prime 5437 := by norm_num

private theorem prime_twentyNineAA_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_twentyNineAA_5813 : Nat.Prime 5813 := by norm_num

private theorem prime_twentyNineAA_5953 : Nat.Prime 5953 := by norm_num

private theorem prime_twentyNineAA_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_twentyNineAA_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_twentyNineAA_7019 : Nat.Prime 7019 := by norm_num

private theorem prime_twentyNineAA_7237 : Nat.Prime 7237 := by norm_num

private theorem prime_twentyNineAA_7309 : Nat.Prime 7309 := by norm_num

private theorem prime_twentyNineAA_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_twentyNineAA_7823 : Nat.Prime 7823 := by norm_num

private theorem prime_twentyNineAA_8147 : Nat.Prime 8147 := by norm_num

private theorem prime_twentyNineAA_8287 : Nat.Prime 8287 := by norm_num

private theorem prime_twentyNineAA_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_twentyNineAA_8539 : Nat.Prime 8539 := by norm_num

private theorem prime_twentyNineAA_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_twentyNineAA_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_twentyNineAA_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_twentyNineAA_9161 : Nat.Prime 9161 := by norm_num

private theorem prime_twentyNineAA_9547 : Nat.Prime 9547 := by norm_num

private theorem prime_twentyNineAA_10289 : Nat.Prime 10289 := by norm_num

private theorem prime_twentyNineAA_10831 : Nat.Prime 10831 := by norm_num

private theorem prime_twentyNineAA_10859 : Nat.Prime 10859 := by norm_num

private theorem prime_twentyNineAA_10957 : Nat.Prime 10957 := by norm_num

private theorem prime_twentyNineAA_11213 : Nat.Prime 11213 := by norm_num

private theorem prime_twentyNineAA_11551 : Nat.Prime 11551 := by norm_num

private theorem prime_twentyNineAA_11923 : Nat.Prime 11923 := by norm_num

private theorem prime_twentyNineAA_12491 : Nat.Prime 12491 := by norm_num

private theorem prime_twentyNineAA_12757 : Nat.Prime 12757 := by norm_num

private theorem prime_twentyNineAA_13003 : Nat.Prime 13003 := by norm_num

private theorem prime_twentyNineAA_14551 : Nat.Prime 14551 := by norm_num

private theorem prime_twentyNineAA_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_twentyNineAA_14813 : Nat.Prime 14813 := by norm_num

private theorem prime_twentyNineAA_15077 : Nat.Prime 15077 := by norm_num

private theorem prime_twentyNineAA_15629 : Nat.Prime 15629 := by norm_num

private theorem prime_twentyNineAA_16433 : Nat.Prime 16433 := by norm_num

private theorem prime_twentyNineAA_16651 : Nat.Prime 16651 := by norm_num

private theorem prime_twentyNineAA_17581 : Nat.Prime 17581 := by norm_num

private theorem prime_twentyNineAA_18523 : Nat.Prime 18523 := by norm_num

private theorem prime_twentyNineAA_18617 : Nat.Prime 18617 := by norm_num

private theorem prime_twentyNineAA_18911 : Nat.Prime 18911 := by norm_num

private theorem prime_twentyNineAA_19423 : Nat.Prime 19423 := by norm_num

private theorem prime_twentyNineAA_20183 : Nat.Prime 20183 := by norm_num

private theorem prime_twentyNineAA_20719 : Nat.Prime 20719 := by norm_num

private theorem prime_twentyNineAA_21323 : Nat.Prime 21323 := by norm_num

private theorem prime_twentyNineAA_22193 : Nat.Prime 22193 := by norm_num

private theorem prime_twentyNineAA_22571 : Nat.Prime 22571 := by norm_num

private theorem prime_twentyNineAA_24859 : Nat.Prime 24859 := by norm_num

private theorem prime_twentyNineAA_26387 : Nat.Prime 26387 := by norm_num

private theorem prime_twentyNineAA_26731 : Nat.Prime 26731 := by norm_num

private theorem prime_twentyNineAA_27367 : Nat.Prime 27367 := by norm_num

private theorem prime_twentyNineAA_27817 : Nat.Prime 27817 := by norm_num

private theorem prime_twentyNineAA_29297 : Nat.Prime 29297 := by norm_num

private theorem prime_twentyNineAA_30109 : Nat.Prime 30109 := by norm_num

private theorem prime_twentyNineAA_30829 : Nat.Prime 30829 := by norm_num

private theorem prime_twentyNineAA_31181 : Nat.Prime 31181 := by norm_num

private theorem prime_twentyNineAA_32299 : Nat.Prime 32299 := by norm_num

private theorem prime_twentyNineAA_32377 : Nat.Prime 32377 := by norm_num

private theorem prime_twentyNineAA_32429 : Nat.Prime 32429 := by norm_num

private theorem prime_twentyNineAA_33289 : Nat.Prime 33289 := by norm_num

private theorem prime_twentyNineAA_33311 : Nat.Prime 33311 := by norm_num

private theorem prime_twentyNineAA_36931 : Nat.Prime 36931 := by norm_num

private theorem prime_twentyNineAA_40487 : Nat.Prime 40487 := by norm_num

private theorem prime_twentyNineAA_42821 : Nat.Prime 42821 := by norm_num

private theorem prime_twentyNineAA_43517 : Nat.Prime 43517 := by norm_num

private theorem prime_twentyNineAA_44131 : Nat.Prime 44131 := by norm_num

private theorem prime_twentyNineAA_44879 : Nat.Prime 44879 := by norm_num

private theorem prime_twentyNineAA_46451 : Nat.Prime 46451 := by norm_num

private theorem prime_twentyNineAA_46831 : Nat.Prime 46831 := by norm_num

private theorem prime_twentyNineAA_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_twentyNineAA_49211 : Nat.Prime 49211 := by norm_num

private theorem prime_twentyNineAA_50857 : Nat.Prime 50857 := by norm_num

private theorem prime_twentyNineAA_51239 : Nat.Prime 51239 := by norm_num

private theorem prime_twentyNineAA_53777 : Nat.Prime 53777 := by norm_num

private theorem prime_twentyNineAA_54013 : Nat.Prime 54013 := by norm_num

private theorem prime_twentyNineAA_54443 : Nat.Prime 54443 := by norm_num

private theorem prime_twentyNineAA_55901 : Nat.Prime 55901 := by norm_num

private theorem prime_twentyNineAA_55921 : Nat.Prime 55921 := by norm_num

private theorem prime_twentyNineAA_58543 : Nat.Prime 58543 := by norm_num

private theorem prime_twentyNineAA_61469 : Nat.Prime 61469 := by norm_num

private theorem prime_twentyNineAA_62927 : Nat.Prime 62927 := by norm_num

private theorem prime_twentyNineAA_63587 : Nat.Prime 63587 := by norm_num

private theorem prime_twentyNineAA_70121 : Nat.Prime 70121 := by norm_num

private theorem prime_twentyNineAA_70321 : Nat.Prime 70321 := by norm_num

private theorem prime_twentyNineAA_73019 : Nat.Prime 73019 := by norm_num

private theorem prime_twentyNineAA_73823 : Nat.Prime 73823 := by norm_num

private theorem prime_twentyNineAA_77201 : Nat.Prime 77201 := by norm_num

private theorem prime_twentyNineAA_82039 : Nat.Prime 82039 := by norm_num

private theorem prime_twentyNineAA_82471 : Nat.Prime 82471 := by norm_num

private theorem prime_twentyNineAA_90731 : Nat.Prime 90731 := by norm_num

private theorem prime_twentyNineAA_92737 : Nat.Prime 92737 := by norm_num

private theorem prime_twentyNineAA_97369 : Nat.Prime 97369 := by norm_num

private theorem prime_twentyNineAA_99391 : Nat.Prime 99391 := by norm_num

private theorem prime_twentyNineAA_101341 : Nat.Prime 101341 := by norm_num

private theorem prime_twentyNineAA_106213 : Nat.Prime 106213 := by norm_num

private theorem prime_twentyNineAA_108827 : Nat.Prime 108827 := by norm_num

private theorem prime_twentyNineAA_109567 : Nat.Prime 109567 := by norm_num

private theorem prime_twentyNineAA_114269 : Nat.Prime 114269 := by norm_num

private theorem prime_twentyNineAA_117959 : Nat.Prime 117959 := by norm_num

private theorem prime_twentyNineAA_121571 : Nat.Prime 121571 := by norm_num

private theorem prime_twentyNineAA_122477 : Nat.Prime 122477 := by norm_num

private theorem prime_twentyNineAA_124771 : Nat.Prime 124771 := by norm_num

private theorem prime_twentyNineAA_124909 : Nat.Prime 124909 := by norm_num

private theorem prime_twentyNineAA_134333 : Nat.Prime 134333 := by norm_num

private theorem prime_twentyNineAA_136099 : Nat.Prime 136099 := by norm_num

private theorem prime_twentyNineAA_137341 : Nat.Prime 137341 := by norm_num

private theorem prime_twentyNineAA_138797 : Nat.Prime 138797 := by norm_num

private theorem prime_twentyNineAA_152287 : Nat.Prime 152287 := by norm_num

private theorem prime_twentyNineAA_159407 : Nat.Prime 159407 := by norm_num

private theorem prime_twentyNineAA_169097 : Nat.Prime 169097 := by norm_num

private theorem prime_twentyNineAA_176047 : Nat.Prime 176047 := by norm_num

private theorem prime_twentyNineAA_176327 : Nat.Prime 176327 := by norm_num

private theorem prime_twentyNineAA_179899 : Nat.Prime 179899 := by norm_num

private theorem prime_twentyNineAA_185599 : Nat.Prime 185599 := by norm_num

private theorem prime_twentyNineAA_204443 : Nat.Prime 204443 := by norm_num

private theorem prime_twentyNineAA_206651 : Nat.Prime 206651 := by norm_num

private theorem prime_twentyNineAA_206749 : Nat.Prime 206749 := by norm_num

private theorem prime_twentyNineAA_234653 : Nat.Prime 234653 := by norm_num

private theorem prime_twentyNineAA_238967 : Nat.Prime 238967 := by norm_num

private theorem prime_twentyNineAA_245339 : Nat.Prime 245339 := by norm_num

private theorem prime_twentyNineAA_254447 : Nat.Prime 254447 := by norm_num

private theorem prime_twentyNineAA_260879 : Nat.Prime 260879 := by norm_num

private theorem prime_twentyNineAA_280183 : Nat.Prime 280183 := by norm_num

private theorem prime_twentyNineAA_295153 : Nat.Prime 295153 := by norm_num

private theorem prime_twentyNineAA_296669 : Nat.Prime 296669 := by norm_num

private theorem prime_twentyNineAA_314243 : Nat.Prime 314243 := by norm_num

private theorem prime_twentyNineAA_315281 : Nat.Prime 315281 := by norm_num

private theorem prime_twentyNineAA_322573 : Nat.Prime 322573 := by norm_num

private theorem prime_twentyNineAA_325807 : Nat.Prime 325807 := by norm_num

private theorem prime_twentyNineAA_330271 : Nat.Prime 330271 := by norm_num

private theorem prime_twentyNineAA_331081 : Nat.Prime 331081 := by norm_num

private theorem prime_twentyNineAA_336529 : Nat.Prime 336529 := by norm_num

private theorem prime_twentyNineAA_339373 : Nat.Prime 339373 := by norm_num

private theorem prime_twentyNineAA_357241 : Nat.Prime 357241 := by norm_num

private theorem prime_twentyNineAA_363719 : Nat.Prime 363719 := by norm_num

private theorem prime_twentyNineAA_369319 : Nat.Prime 369319 := by norm_num

private theorem prime_twentyNineAA_369331 : Nat.Prime 369331 := by norm_num

private theorem prime_twentyNineAA_375593 : Nat.Prime 375593 := by norm_num

private theorem prime_twentyNineAA_376627 : Nat.Prime 376627 := by norm_num

private theorem prime_twentyNineAA_389273 : Nat.Prime 389273 := by norm_num

private theorem prime_twentyNineAA_393697 : Nat.Prime 393697 := by norm_num

private theorem prime_twentyNineAA_411491 : Nat.Prime 411491 := by norm_num

private theorem prime_twentyNineAA_433571 : Nat.Prime 433571 := by norm_num

private theorem prime_twentyNineAA_446473 : Nat.Prime 446473 := by norm_num

private theorem prime_twentyNineAA_471817 : Nat.Prime 471817 := by norm_num

private theorem prime_twentyNineAA_493877 : Nat.Prime 493877 := by norm_num

private theorem prime_twentyNineAA_504269 : Nat.Prime 504269 := by norm_num

private theorem prime_twentyNineAA_510683 : Nat.Prime 510683 := by norm_num

private theorem prime_twentyNineAA_530443 : Nat.Prime 530443 := by norm_num

private theorem prime_twentyNineAA_549257 : Nat.Prime 549257 := by norm_num

private theorem prime_twentyNineAA_573863 : Nat.Prime 573863 := by norm_num

private theorem prime_twentyNineAA_578573 : Nat.Prime 578573 := by norm_num

private theorem prime_twentyNineAA_598799 : Nat.Prime 598799 := by norm_num

private theorem prime_twentyNineAA_614611 : Nat.Prime 614611 := by norm_num

private theorem prime_twentyNineAA_656479 : Nat.Prime 656479 := by norm_num

private theorem prime_twentyNineAA_680707 : Nat.Prime 680707 := by norm_num

private theorem prime_twentyNineAA_709729 : Nat.Prime 709729 := by norm_num

private theorem prime_twentyNineAA_731047 : Nat.Prime 731047 := by norm_num

private theorem prime_twentyNineAA_762653 : Nat.Prime 762653 := by norm_num

private theorem prime_twentyNineAA_769147 : Nat.Prime 769147 := by norm_num

private theorem prime_twentyNineAA_770041 : Nat.Prime 770041 := by norm_num

private theorem prime_twentyNineAA_772853 : Nat.Prime 772853 := by norm_num

private theorem prime_twentyNineAA_868051 : Nat.Prime 868051 := by norm_num

private theorem prime_twentyNineAA_870407 : Nat.Prime 870407 := by norm_num

private theorem prime_twentyNineAA_894139 : Nat.Prime 894139 := by norm_num

private theorem prime_twentyNineAA_942199 : Nat.Prime 942199 := by norm_num

private theorem prime_twentyNineAA_951101 : Nat.Prime 951101 := by norm_num

private theorem prime_twentyNineAA_980489 : Nat.Prime 980489 := by norm_num

private theorem prime_twentyNineAA_987023 : Nat.Prime 987023 := by norm_num

private theorem prime_twentyNineAA_1110313 : Nat.Prime 1110313 := by norm_num

private theorem prime_twentyNineAA_1110367 : Nat.Prime 1110367 := by norm_num

private theorem prime_twentyNineAA_1249403 : Nat.Prime 1249403 := by norm_num

private theorem prime_twentyNineAA_1262087 : Nat.Prime 1262087 := by norm_num

private theorem prime_twentyNineAA_1362371 : Nat.Prime 1362371 := by norm_num

private theorem prime_twentyNineAA_1373159 : Nat.Prime 1373159 := by norm_num

private theorem prime_twentyNineAA_1420847 : Nat.Prime 1420847 := by norm_num

private theorem prime_twentyNineAA_1480643 : Nat.Prime 1480643 := by norm_num

private theorem prime_twentyNineAA_1486003 : Nat.Prime 1486003 := by norm_num

private theorem prime_twentyNineAA_1496507 : Nat.Prime 1496507 := by norm_num

private theorem prime_twentyNineAA_1644173 : Nat.Prime 1644173 := by norm_num

private theorem prime_twentyNineAA_1663027 : Nat.Prime 1663027 := by norm_num

private theorem prime_twentyNineAA_1683467 : Nat.Prime 1683467 := by norm_num

private theorem prime_twentyNineAA_1795979 : Nat.Prime 1795979 := by norm_num

private theorem prime_twentyNineAA_1879607 : Nat.Prime 1879607 := by norm_num

private theorem prime_twentyNineAA_1903877 : Nat.Prime 1903877 := by norm_num

private theorem prime_twentyNineAA_1935893 : Nat.Prime 1935893 := by norm_num

private theorem prime_twentyNineAA_2006579 : Nat.Prime 2006579 := by norm_num

private theorem prime_twentyNineAA_2079739 : Nat.Prime 2079739 := by norm_num

private theorem prime_twentyNineAA_2198293 : Nat.Prime 2198293 := by norm_num

private theorem prime_twentyNineAA_2286629 : Nat.Prime 2286629 := by norm_num

private theorem prime_twentyNineAA_2310157 : Nat.Prime 2310157 := by norm_num

private theorem prime_twentyNineAA_2316757 : Nat.Prime 2316757 := by norm_num

private theorem prime_twentyNineAA_2329291 : Nat.Prime 2329291 := by norm_num

private theorem prime_twentyNineAA_2459761 : Nat.Prime 2459761 := by norm_num

private theorem prime_twentyNineAA_2658871 : Nat.Prime 2658871 := by norm_num

private theorem prime_twentyNineAA_2783909 : Nat.Prime 2783909 := by norm_num

private theorem prime_twentyNineAA_2818817 : Nat.Prime 2818817 := by norm_num

private theorem prime_twentyNineAA_2888807 : Nat.Prime 2888807 := by norm_num

private theorem prime_twentyNineAA_2998169 : Nat.Prime 2998169 := by norm_num

private theorem prime_twentyNineAA_3229319 : Nat.Prime 3229319 := by norm_num

private theorem prime_twentyNineAA_3237827 : Nat.Prime 3237827 := by norm_num

private theorem prime_twentyNineAA_3615581 : Nat.Prime 3615581 := by norm_num

private theorem prime_twentyNineAA_4006463 : Nat.Prime 4006463 := by norm_num

private theorem prime_twentyNineAA_4573141 : Nat.Prime 4573141 := by norm_num

private theorem prime_twentyNineAA_4711361 : Nat.Prime 4711361 := by norm_num

private theorem prime_twentyNineAA_4773451 : Nat.Prime 4773451 := by norm_num

private theorem prime_twentyNineAA_4829423 : Nat.Prime 4829423 := by norm_num

private theorem prime_twentyNineAA_4903043 : Nat.Prime 4903043 := by norm_num

private theorem prime_twentyNineAA_5068927 : Nat.Prime 5068927 := by norm_num

private theorem prime_twentyNineAA_5935481 : Nat.Prime 5935481 := by norm_num

private theorem prime_twentyNineAA_6344777 : Nat.Prime 6344777 := by norm_num

private theorem prime_twentyNineAA_6465911 : Nat.Prime 6465911 := by norm_num

private theorem prime_twentyNineAA_6820277 : Nat.Prime 6820277 := by norm_num

private theorem prime_twentyNineAA_6946633 : Nat.Prime 6946633 := by norm_num

private theorem prime_twentyNineAA_7212389 : Nat.Prime 7212389 := by norm_num

private theorem prime_twentyNineAA_7291489 : Nat.Prime 7291489 := by norm_num

private theorem prime_twentyNineAA_7468319 : Nat.Prime 7468319 := by norm_num

private theorem prime_twentyNineAA_7519217 : Nat.Prime 7519217 := by norm_num

private theorem prime_twentyNineAA_7562473 : Nat.Prime 7562473 := by norm_num

private theorem prime_twentyNineAA_7616513 : Nat.Prime 7616513 := by norm_num

private theorem prime_twentyNineAA_7738259 : Nat.Prime 7738259 := by norm_num

private theorem prime_twentyNineAA_7972669 : Nat.Prime 7972669 := by norm_num

private theorem prime_twentyNineAA_8303459 : Nat.Prime 8303459 := by norm_num

private theorem prime_twentyNineAA_8646667 : Nat.Prime 8646667 := by norm_num

private theorem prime_twentyNineAA_9854753 : Nat.Prime 9854753 := by norm_num

private theorem prime_twentyNineAA_9885049 : Nat.Prime 9885049 := by norm_num

private theorem prime_twentyNineAA_9910123 : Nat.Prime 9910123 := by norm_num

private theorem prime_twentyNineAA_10229861 : Nat.Prime 10229861 := by
  apply lucas_primality 10229861 (2 : ZMod 10229861)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (617, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (617, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) = 10229861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_617
      · exact prime_twentyNineAA_829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10229861) ^ 5114930 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10229861) ^ 2045972 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10229861) ^ 16580 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10229861) ^ 12340 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_11068399 : Nat.Prime 11068399 := by
  apply lucas_primality 11068399 (3 : ZMod 11068399)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (55901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (55901, 1)] : List FactorBlock).map factorBlockValue).prod) = 11068399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_55901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11068399) ^ 5534199 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11068399) ^ 3689466 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11068399) ^ 1006218 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11068399) ^ 198 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_11203547 : Nat.Prime 11203547 := by
  apply lucas_primality 11203547 (2 : ZMod 11203547)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (941, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (941, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) = 11203547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_941
      · exact prime_twentyNineAA_5953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11203547) ^ 5601773 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11203547) ^ 11906 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11203547) ^ 1882 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_11683141 : Nat.Prime 11683141 := by
  apply lucas_primality 11683141 (6 : ZMod 11683141)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (27817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (27817, 1)] : List FactorBlock).map factorBlockValue).prod) = 11683141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_27817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11683141) ^ 5841570 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11683141) ^ 3894380 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11683141) ^ 2336628 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11683141) ^ 1669020 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 11683141) ^ 420 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12102457 : Nat.Prime 12102457 := by
  apply lucas_primality 12102457 (5 : ZMod 12102457)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (504269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (504269, 1)] : List FactorBlock).map factorBlockValue).prod) = 12102457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_504269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12102457) ^ 6051228 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12102457) ^ 4034152 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12102457) ^ 24 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12271439 : Nat.Prime 12271439 := by
  apply lucas_primality 12271439 (11 : ZMod 12271439)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (181, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (181, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 12271439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_109
      · exact prime_twentyNineAA_181
      · exact prime_t64_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12271439) ^ 6135719 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12271439) ^ 112582 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12271439) ^ 67798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 12271439) ^ 39458 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12659323 : Nat.Prime 12659323 := by
  apply lucas_primality 12659323 (2 : ZMod 12659323)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (9547, 1)] : List FactorBlock).map factorBlockValue).prod) = 12659323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_twentyNineAA_9547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12659323) ^ 6329661 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659323) ^ 4219774 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659323) ^ 973794 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659323) ^ 744666 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659323) ^ 1326 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12775123 : Nat.Prime 12775123 := by
  apply lucas_primality 12775123 (2 : ZMod 12775123)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (709729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (709729, 1)] : List FactorBlock).map factorBlockValue).prod) = 12775123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_709729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12775123) ^ 6387561 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12775123) ^ 4258374 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12775123) ^ 18 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12931823 : Nat.Prime 12931823 := by
  apply lucas_primality 12931823 (5 : ZMod 12931823)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6465911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6465911, 1)] : List FactorBlock).map factorBlockValue).prod) = 12931823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_6465911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 12931823) ^ 6465911 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12931823) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_13807691 : Nat.Prime 13807691 := by
  apply lucas_primality 13807691 (2 : ZMod 13807691)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (106213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (106213, 1)] : List FactorBlock).map factorBlockValue).prod) = 13807691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyNineAA_106213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13807691) ^ 6903845 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807691) ^ 2761538 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807691) ^ 1062130 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13807691) ^ 130 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_13980277 : Nat.Prime 13980277 := by
  apply lucas_primality 13980277 (5 : ZMod 13980277)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (19, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (19, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 13980277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentyNineAA_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13980277) ^ 6990138 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13980277) ^ 4660092 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13980277) ^ 735804 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 13980277) ^ 18468 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_14145389 : Nat.Prime 14145389 := by
  apply lucas_primality 14145389 (2 : ZMod 14145389)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (197, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (197, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 14145389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_197
      · exact prime_twentyNineAA_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14145389) ^ 7072694 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14145389) ^ 487772 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14145389) ^ 71804 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14145389) ^ 22852 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_15233027 : Nat.Prime 15233027 := by
  apply lucas_primality 15233027 (2 : ZMod 15233027)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7616513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7616513, 1)] : List FactorBlock).map factorBlockValue).prod) = 15233027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_7616513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 15233027) ^ 7616513 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 15233027) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_16020127 : Nat.Prime 16020127 := by
  apply lucas_primality 16020127 (3 : ZMod 16020127)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (296669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (296669, 1)] : List FactorBlock).map factorBlockValue).prod) = 16020127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_296669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16020127) ^ 8010063 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16020127) ^ 5340042 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 16020127) ^ 54 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_18268321 : Nat.Prime 18268321 := by
  apply lucas_primality 18268321 (13 : ZMod 18268321)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (5437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (5437, 1)] : List FactorBlock).map factorBlockValue).prod) = 18268321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_5437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18268321) ^ 9134160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 18268321) ^ 6089440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 18268321) ^ 3653664 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 18268321) ^ 2609760 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 18268321) ^ 3360 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_19212269 : Nat.Prime 19212269 := by
  apply lucas_primality 19212269 (2 : ZMod 19212269)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (23, 1), (29, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (23, 1), (29, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 19212269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_twentyNineAA_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19212269) ^ 9606134 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19212269) ^ 1011172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19212269) ^ 835316 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19212269) ^ 662492 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19212269) ^ 50692 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_21838867 : Nat.Prime 21838867 := by
  apply lucas_primality 21838867 (7 : ZMod 21838867)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (27367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (27367, 1)] : List FactorBlock).map factorBlockValue).prod) = 21838867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_twentyNineAA_27367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21838867) ^ 10919433 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21838867) ^ 7279622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21838867) ^ 3119838 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21838867) ^ 1149414 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 21838867) ^ 798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_21970829 : Nat.Prime 21970829 := by
  apply lucas_primality 21970829 (2 : ZMod 21970829)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (281, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (281, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) = 21970829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentyNineAA_281
      · exact prime_twentyNineAA_1777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21970829) ^ 10985414 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21970829) ^ 1997348 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21970829) ^ 78188 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21970829) ^ 12364 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_22034891 : Nat.Prime 22034891 := by
  apply lucas_primality 22034891 (2 : ZMod 22034891)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (227, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (227, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 22034891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_227
      · exact prime_twentyNineAA_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22034891) ^ 11017445 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22034891) ^ 4406978 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22034891) ^ 1296170 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22034891) ^ 97070 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22034891) ^ 38590 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_22474649 : Nat.Prime 22474649 := by
  apply lucas_primality 22474649 (3 : ZMod 22474649)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (47, 1), (8539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (47, 1), (8539, 1)] : List FactorBlock).map factorBlockValue).prod) = 22474649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_twentyNineAA_8539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22474649) ^ 11237324 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22474649) ^ 3210664 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22474649) ^ 478184 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 22474649) ^ 2632 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_23580397 : Nat.Prime 23580397 := by
  apply lucas_primality 23580397 (2 : ZMod 23580397)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (37, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (37, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 23580397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_twentyNineAA_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23580397) ^ 11790198 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23580397) ^ 7860132 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23580397) ^ 3368628 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23580397) ^ 637308 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23580397) ^ 83916 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_26021519 : Nat.Prime 26021519 := by
  apply lucas_primality 26021519 (17 : ZMod 26021519)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1597, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1597, 1), (8147, 1)] : List FactorBlock).map factorBlockValue).prod) = 26021519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_1597
      · exact prime_twentyNineAA_8147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 26021519) ^ 13010759 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 26021519) ^ 16294 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 26021519) ^ 3194 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_27150317 : Nat.Prime 27150317 := by
  apply lucas_primality 27150317 (2 : ZMod 27150317)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (357241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (357241, 1)] : List FactorBlock).map factorBlockValue).prod) = 27150317 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentyNineAA_357241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27150317) ^ 13575158 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27150317) ^ 1428964 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27150317) ^ 76 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_27438847 : Nat.Prime 27438847 := by
  apply lucas_primality 27438847 (3 : ZMod 27438847)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4573141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4573141, 1)] : List FactorBlock).map factorBlockValue).prod) = 27438847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_4573141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27438847) ^ 13719423 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27438847) ^ 9146282 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27438847) ^ 6 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_27615383 : Nat.Prime 27615383 := by
  apply lucas_primality 27615383 (5 : ZMod 27615383)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13807691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13807691, 1)] : List FactorBlock).map factorBlockValue).prod) = 27615383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_13807691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 27615383) ^ 13807691 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 27615383) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_31785773 : Nat.Prime 31785773 := by
  apply lucas_primality 31785773 (2 : ZMod 31785773)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (181, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (181, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) = 31785773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_twentyNineAA_181
      · exact prime_twentyNineAA_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31785773) ^ 15892886 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31785773) ^ 739204 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31785773) ^ 175612 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31785773) ^ 31132 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_31993901 : Nat.Prime 31993901 := by
  apply lucas_primality 31993901 (2 : ZMod 31993901)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) = 31993901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_twentyNineAA_8647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31993901) ^ 15996950 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31993901) ^ 6398780 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31993901) ^ 864700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31993901) ^ 3700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_32341723 : Nat.Prime 32341723 := by
  apply lucas_primality 32341723 (2 : ZMod 32341723)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (770041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (770041, 1)] : List FactorBlock).map factorBlockValue).prod) = 32341723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyNineAA_770041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32341723) ^ 16170861 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32341723) ^ 10780574 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32341723) ^ 4620246 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32341723) ^ 42 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_39300563 : Nat.Prime 39300563 := by
  apply lucas_primality 39300563 (2 : ZMod 39300563)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (367, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (367, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) = 39300563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_367
      · exact prime_twentyNineAA_7649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39300563) ^ 19650281 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39300563) ^ 5614366 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39300563) ^ 107086 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 39300563) ^ 5138 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_39463439 : Nat.Prime 39463439 := by
  apply lucas_primality 39463439 (7 : ZMod 39463439)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2818817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2818817, 1)] : List FactorBlock).map factorBlockValue).prod) = 39463439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_2818817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 39463439) ^ 19731719 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39463439) ^ 5637634 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 39463439) ^ 14 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_44949299 : Nat.Prime 44949299 := by
  apply lucas_primality 44949299 (2 : ZMod 44949299)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22474649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22474649, 1)] : List FactorBlock).map factorBlockValue).prod) = 44949299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_22474649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44949299) ^ 22474649 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 44949299) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_45210467 : Nat.Prime 45210467 := by
  apply lucas_primality 45210467 (2 : ZMod 45210467)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3229319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3229319, 1)] : List FactorBlock).map factorBlockValue).prod) = 45210467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_3229319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45210467) ^ 22605233 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45210467) ^ 6458638 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 45210467) ^ 14 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_45242713 : Nat.Prime 45242713 := by
  apply lucas_primality 45242713 (5 : ZMod 45242713)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (17, 1), (37, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (17, 1), (37, 2)] : List FactorBlock).map factorBlockValue).prod) = 45242713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_37
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45242713) ^ 22621356 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 45242713) ^ 15080904 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 45242713) ^ 2661336 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 45242713) ^ 1222776 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_50110363 : Nat.Prime 50110363 := by
  apply lucas_primality 50110363 (3 : ZMod 50110363)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2783909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2783909, 1)] : List FactorBlock).map factorBlockValue).prod) = 50110363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_2783909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50110363) ^ 25055181 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 50110363) ^ 16703454 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 50110363) ^ 18 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_54863833 : Nat.Prime 54863833 := by
  apply lucas_primality 54863833 (5 : ZMod 54863833)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (99391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (99391, 1)] : List FactorBlock).map factorBlockValue).prod) = 54863833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_twentyNineAA_99391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 54863833) ^ 27431916 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 54863833) ^ 18287944 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 54863833) ^ 2385384 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 54863833) ^ 552 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_56201281 : Nat.Prime 56201281 := by
  apply lucas_primality 56201281 (7 : ZMod 56201281)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (58543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (58543, 1)] : List FactorBlock).map factorBlockValue).prod) = 56201281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_58543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 56201281) ^ 28100640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 56201281) ^ 18733760 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 56201281) ^ 11240256 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 56201281) ^ 960 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_57784057 : Nat.Prime 57784057 := by
  apply lucas_primality 57784057 (15 : ZMod 57784057)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (47, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (47, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) = 57784057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_47
      · exact prime_twentyNineAA_4657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 57784057) ^ 28892028 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (15 : ZMod 57784057) ^ 19261352 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (15 : ZMod 57784057) ^ 5253096 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (15 : ZMod 57784057) ^ 1229448 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (15 : ZMod 57784057) ^ 12408 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_70517107 : Nat.Prime 70517107 := by
  apply lucas_primality 70517107 (11 : ZMod 70517107)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (32377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (32377, 1)] : List FactorBlock).map factorBlockValue).prod) = 70517107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_32377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 70517107) ^ 35258553 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 70517107) ^ 23505702 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 70517107) ^ 6410646 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 70517107) ^ 2178 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_71967503 : Nat.Prime 71967503 := by
  apply lucas_primality 71967503 (5 : ZMod 71967503)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (467, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (467, 1), (2657, 1)] : List FactorBlock).map factorBlockValue).prod) = 71967503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_467
      · exact prime_twentyNineAA_2657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71967503) ^ 35983751 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71967503) ^ 2481638 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71967503) ^ 154106 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 71967503) ^ 27086 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_72614743 : Nat.Prime 72614743 := by
  apply lucas_primality 72614743 (3 : ZMod 72614743)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12102457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12102457, 1)] : List FactorBlock).map factorBlockValue).prod) = 72614743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_12102457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72614743) ^ 36307371 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72614743) ^ 24204914 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72614743) ^ 6 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_72751339 : Nat.Prime 72751339 := by
  apply lucas_primality 72751339 (2 : ZMod 72751339)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (122477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (122477, 1)] : List FactorBlock).map factorBlockValue).prod) = 72751339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_122477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72751339) ^ 36375669 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72751339) ^ 24250446 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72751339) ^ 6613758 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72751339) ^ 594 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_74089637 : Nat.Prime 74089637 := by
  apply lucas_primality 74089637 (2 : ZMod 74089637)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (260879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (260879, 1)] : List FactorBlock).map factorBlockValue).prod) = 74089637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_71
      · exact prime_twentyNineAA_260879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74089637) ^ 37044818 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74089637) ^ 1043516 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74089637) ^ 284 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_78926879 : Nat.Prime 78926879 := by
  apply lucas_primality 78926879 (11 : ZMod 78926879)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39463439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39463439, 1)] : List FactorBlock).map factorBlockValue).prod) = 78926879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_39463439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 78926879) ^ 39463439 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 78926879) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_79490881 : Nat.Prime 79490881 := by
  apply lucas_primality 79490881 (13 : ZMod 79490881)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) = 79490881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_3943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 79490881) ^ 39745440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 79490881) ^ 26496960 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 79490881) ^ 15898176 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 79490881) ^ 11355840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 79490881) ^ 20160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_87669019 : Nat.Prime 87669019 := by
  apply lucas_primality 87669019 (2 : ZMod 87669019)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (673, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (673, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 87669019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_673
      · exact prime_twentyNineAA_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87669019) ^ 43834509 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669019) ^ 29223006 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669019) ^ 130266 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87669019) ^ 12114 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_93967021 : Nat.Prime 93967021 := by
  apply lucas_primality 93967021 (2 : ZMod 93967021)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (24859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (24859, 1)] : List FactorBlock).map factorBlockValue).prod) = 93967021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_24859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93967021) ^ 46983510 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93967021) ^ 31322340 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93967021) ^ 18793404 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93967021) ^ 13423860 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93967021) ^ 3780 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_95672029 : Nat.Prime 95672029 := by
  apply lucas_primality 95672029 (2 : ZMod 95672029)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7972669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7972669, 1)] : List FactorBlock).map factorBlockValue).prod) = 95672029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_7972669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 95672029) ^ 47836014 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95672029) ^ 31890676 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 95672029) ^ 12 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_99533389 : Nat.Prime 99533389 := by
  apply lucas_primality 99533389 (2 : ZMod 99533389)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (757, 1), (10957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (757, 1), (10957, 1)] : List FactorBlock).map factorBlockValue).prod) = 99533389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_757
      · exact prime_twentyNineAA_10957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 99533389) ^ 49766694 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99533389) ^ 33177796 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99533389) ^ 131484 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 99533389) ^ 9084 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_104828879 : Nat.Prime 104828879 := by
  apply lucas_primality 104828879 (7 : ZMod 104828879)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (680707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (680707, 1)] : List FactorBlock).map factorBlockValue).prod) = 104828879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyNineAA_680707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 104828879) ^ 52414439 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 104828879) ^ 14975554 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 104828879) ^ 9529898 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 104828879) ^ 154 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_115357391 : Nat.Prime 115357391 := by
  apply lucas_primality 115357391 (7 : ZMod 115357391)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (59, 1), (4547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (59, 1), (4547, 1)] : List FactorBlock).map factorBlockValue).prod) = 115357391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_t64_59
      · exact prime_twentyNineAA_4547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 115357391) ^ 57678695 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 115357391) ^ 23071478 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 115357391) ^ 2682730 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 115357391) ^ 1955210 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 115357391) ^ 25370 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_140886899 : Nat.Prime 140886899 := by
  apply lucas_primality 140886899 (2 : ZMod 140886899)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1903877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1903877, 1)] : List FactorBlock).map factorBlockValue).prod) = 140886899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_twentyNineAA_1903877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140886899) ^ 70443449 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 140886899) ^ 3807754 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 140886899) ^ 74 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_147376259 : Nat.Prime 147376259 := by
  apply lucas_primality 147376259 (2 : ZMod 147376259)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (263, 1), (280183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (263, 1), (280183, 1)] : List FactorBlock).map factorBlockValue).prod) = 147376259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_263
      · exact prime_twentyNineAA_280183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 147376259) ^ 73688129 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 147376259) ^ 560366 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 147376259) ^ 526 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_152687473 : Nat.Prime 152687473 := by
  apply lucas_primality 152687473 (5 : ZMod 152687473)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (17, 1), (26731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (17, 1), (26731, 1)] : List FactorBlock).map factorBlockValue).prod) = 152687473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_twentyNineAA_26731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 152687473) ^ 76343736 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 152687473) ^ 50895824 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 152687473) ^ 21812496 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 152687473) ^ 8981616 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 152687473) ^ 5712 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_176692181 : Nat.Prime 176692181 := by
  apply lucas_primality 176692181 (2 : ZMod 176692181)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1262087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1262087, 1)] : List FactorBlock).map factorBlockValue).prod) = 176692181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_1262087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 176692181) ^ 88346090 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 176692181) ^ 35338436 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 176692181) ^ 25241740 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 176692181) ^ 140 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_191963407 : Nat.Prime 191963407 := by
  apply lucas_primality 191963407 (3 : ZMod 191963407)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31993901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31993901, 1)] : List FactorBlock).map factorBlockValue).prod) = 191963407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_31993901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 191963407) ^ 95981703 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 191963407) ^ 63987802 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 191963407) ^ 6 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_204346231 : Nat.Prime 204346231 := by
  apply lucas_primality 204346231 (6 : ZMod 204346231)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (101, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (101, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) = 204346231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_101
      · exact prime_twentyNineAA_6131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 204346231) ^ 102173115 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 204346231) ^ 68115410 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 204346231) ^ 40869246 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 204346231) ^ 18576930 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 204346231) ^ 2023230 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 204346231) ^ 33330 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_204401969 : Nat.Prime 204401969 := by
  apply lucas_primality 204401969 (3 : ZMod 204401969)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (12775123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (12775123, 1)] : List FactorBlock).map factorBlockValue).prod) = 204401969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_12775123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 204401969) ^ 102200984 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 204401969) ^ 16 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_209657759 : Nat.Prime 209657759 := by
  apply lucas_primality 209657759 (11 : ZMod 209657759)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (104828879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (104828879, 1)] : List FactorBlock).map factorBlockValue).prod) = 209657759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_104828879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 209657759) ^ 104828879 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 209657759) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_212246141 : Nat.Prime 212246141 := by
  apply lucas_primality 212246141 (2 : ZMod 212246141)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (134333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (134333, 1)] : List FactorBlock).map factorBlockValue).prod) = 212246141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_twentyNineAA_134333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 212246141) ^ 106123070 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 212246141) ^ 42449228 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 212246141) ^ 2686660 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 212246141) ^ 1580 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_237976093 : Nat.Prime 237976093 := by
  apply lucas_primality 237976093 (5 : ZMod 237976093)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (397, 1), (16651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (397, 1), (16651, 1)] : List FactorBlock).map factorBlockValue).prod) = 237976093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_397
      · exact prime_twentyNineAA_16651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237976093) ^ 118988046 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 237976093) ^ 79325364 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 237976093) ^ 599436 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 237976093) ^ 14292 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_266853049 : Nat.Prime 266853049 := by
  apply lucas_primality 266853049 (13 : ZMod 266853049)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (197, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (197, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 266853049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_197
      · exact prime_twentyNineAA_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 266853049) ^ 133426524 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 266853049) ^ 88951016 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 266853049) ^ 38121864 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 266853049) ^ 24259368 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 266853049) ^ 1354584 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 266853049) ^ 364056 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_274019411 : Nat.Prime 274019411 := by
  apply lucas_primality 274019411 (2 : ZMod 274019411)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (37, 1), (241, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (37, 1), (241, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 274019411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_twentyNineAA_241
      · exact prime_t64_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274019411) ^ 137009705 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 274019411) ^ 54803882 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 274019411) ^ 39145630 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 274019411) ^ 7405930 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 274019411) ^ 1137010 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 274019411) ^ 624190 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_281840327 : Nat.Prime 281840327 := by
  apply lucas_primality 281840327 (5 : ZMod 281840327)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (2658871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (2658871, 1)] : List FactorBlock).map factorBlockValue).prod) = 281840327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentyNineAA_2658871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 281840327) ^ 140920163 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 281840327) ^ 5317742 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 281840327) ^ 106 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_284903089 : Nat.Prime 284903089 := by
  apply lucas_primality 284903089 (19 : ZMod 284903089)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5935481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5935481, 1)] : List FactorBlock).map factorBlockValue).prod) = 284903089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_5935481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 284903089) ^ 142451544 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 284903089) ^ 94967696 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 284903089) ^ 48 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_334080829 : Nat.Prime 334080829 := by
  apply lucas_primality 334080829 (7 : ZMod 334080829)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (167, 1), (18523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (167, 1), (18523, 1)] : List FactorBlock).map factorBlockValue).prod) = 334080829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_167
      · exact prime_twentyNineAA_18523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 334080829) ^ 167040414 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 334080829) ^ 111360276 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 334080829) ^ 2000484 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 334080829) ^ 18036 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_367486159 : Nat.Prime 367486159 := by
  apply lucas_primality 367486159 (3 : ZMod 367486159)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4711361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4711361, 1)] : List FactorBlock).map factorBlockValue).prod) = 367486159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyNineAA_4711361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 367486159) ^ 183743079 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 367486159) ^ 122495386 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 367486159) ^ 28268166 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 367486159) ^ 78 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_376325567 : Nat.Prime 376325567 := by
  apply lucas_primality 376325567 (5 : ZMod 376325567)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (11068399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (11068399, 1)] : List FactorBlock).map factorBlockValue).prod) = 376325567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyNineAA_11068399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 376325567) ^ 188162783 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 376325567) ^ 22136798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 376325567) ^ 34 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_408803939 : Nat.Prime 408803939 := by
  apply lucas_primality 408803939 (2 : ZMod 408803939)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (204401969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (204401969, 1)] : List FactorBlock).map factorBlockValue).prod) = 408803939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_204401969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 408803939) ^ 204401969 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 408803939) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_434334487 : Nat.Prime 434334487 := by
  apply lucas_primality 434334487 (3 : ZMod 434334487)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (1683467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (1683467, 1)] : List FactorBlock).map factorBlockValue).prod) = 434334487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_1683467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 434334487) ^ 217167243 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 434334487) ^ 144778162 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 434334487) ^ 10100802 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 434334487) ^ 258 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_466655297 : Nat.Prime 466655297 := by
  apply lucas_primality 466655297 (3 : ZMod 466655297)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7291489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7291489, 1)] : List FactorBlock).map factorBlockValue).prod) = 466655297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_7291489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 466655297) ^ 233327648 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 466655297) ^ 64 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_540218179 : Nat.Prime 540218179 := by
  apply lucas_primality 540218179 (3 : ZMod 540218179)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1487, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1487, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) = 540218179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_1487
      · exact prime_twentyNineAA_20183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 540218179) ^ 270109089 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 540218179) ^ 180072726 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 540218179) ^ 363294 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 540218179) ^ 26766 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_561284881 : Nat.Prime 561284881 := by
  apply lucas_primality 561284881 (17 : ZMod 561284881)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (179899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (179899, 1)] : List FactorBlock).map factorBlockValue).prod) = 561284881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyNineAA_179899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 561284881) ^ 280642440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 561284881) ^ 187094960 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 561284881) ^ 112256976 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 561284881) ^ 43175760 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 561284881) ^ 3120 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_563019781 : Nat.Prime 563019781 := by
  apply lucas_primality 563019781 (10 : ZMod 563019781)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (493877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (493877, 1)] : List FactorBlock).map factorBlockValue).prod) = 563019781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_twentyNineAA_493877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 563019781) ^ 281509890 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 563019781) ^ 187673260 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 563019781) ^ 112603956 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 563019781) ^ 29632620 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 563019781) ^ 1140 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_582666893 : Nat.Prime 582666893 := by
  apply lucas_primality 582666893 (2 : ZMod 582666893)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (762653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (762653, 1)] : List FactorBlock).map factorBlockValue).prod) = 582666893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_191
      · exact prime_twentyNineAA_762653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 582666893) ^ 291333446 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 582666893) ^ 3050612 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 582666893) ^ 764 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_600436063 : Nat.Prime 600436063 := by
  apply lucas_primality 600436063 (3 : ZMod 600436063)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (41, 1), (42821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (41, 1), (42821, 1)] : List FactorBlock).map factorBlockValue).prod) = 600436063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_41
      · exact prime_twentyNineAA_42821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 600436063) ^ 300218031 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 600436063) ^ 200145354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 600436063) ^ 31601898 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 600436063) ^ 14644782 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 600436063) ^ 14022 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_619053551 : Nat.Prime 619053551 := by
  apply lucas_primality 619053551 (7 : ZMod 619053551)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (113, 1), (109567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (113, 1), (109567, 1)] : List FactorBlock).map factorBlockValue).prod) = 619053551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_113
      · exact prime_twentyNineAA_109567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 619053551) ^ 309526775 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 619053551) ^ 123810710 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 619053551) ^ 5478350 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 619053551) ^ 5650 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_737147771 : Nat.Prime 737147771 := by
  apply lucas_primality 737147771 (2 : ZMod 737147771)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (1249403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (1249403, 1)] : List FactorBlock).map factorBlockValue).prod) = 737147771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_59
      · exact prime_twentyNineAA_1249403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 737147771) ^ 368573885 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 737147771) ^ 147429554 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 737147771) ^ 12494030 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 737147771) ^ 590 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_773603081 : Nat.Prime 773603081 := by
  apply lucas_primality 773603081 (3 : ZMod 773603081)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (411491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (411491, 1)] : List FactorBlock).map factorBlockValue).prod) = 773603081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_47
      · exact prime_twentyNineAA_411491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 773603081) ^ 386801540 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 773603081) ^ 154720616 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 773603081) ^ 16459640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 773603081) ^ 1880 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_864256643 : Nat.Prime 864256643 := by
  apply lucas_primality 864256643 (2 : ZMod 864256643)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (787, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (787, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) = 864256643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_787
      · exact prime_twentyNineAA_32299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 864256643) ^ 432128321 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 864256643) ^ 50838626 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 864256643) ^ 1098166 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 864256643) ^ 26758 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_923266907 : Nat.Prime 923266907 := by
  apply lucas_primality 923266907 (2 : ZMod 923266907)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (331, 1), (82039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (331, 1), (82039, 1)] : List FactorBlock).map factorBlockValue).prod) = 923266907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyNineAA_331
      · exact prime_twentyNineAA_82039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 923266907) ^ 461633453 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 923266907) ^ 54309818 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 923266907) ^ 2789326 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 923266907) ^ 11254 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_990775063 : Nat.Prime 990775063 := by
  apply lucas_primality 990775063 (3 : ZMod 990775063)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (3237827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (3237827, 1)] : List FactorBlock).map factorBlockValue).prod) = 990775063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyNineAA_3237827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 990775063) ^ 495387531 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 990775063) ^ 330258354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 990775063) ^ 58280886 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 990775063) ^ 306 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1027965881 : Nat.Prime 1027965881 := by
  apply lucas_primality 1027965881 (6 : ZMod 1027965881)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (254447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (254447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027965881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_101
      · exact prime_twentyNineAA_254447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1027965881) ^ 513982940 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027965881) ^ 205593176 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027965881) ^ 10177880 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1027965881) ^ 4040 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1037970761 : Nat.Prime 1037970761 := by
  apply lucas_primality 1037970761 (3 : ZMod 1037970761)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (41, 1), (33311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (41, 1), (33311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1037970761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_41
      · exact prime_twentyNineAA_33311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1037970761) ^ 518985380 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037970761) ^ 207594152 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037970761) ^ 54630040 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037970761) ^ 25316360 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1037970761) ^ 31160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1232632421 : Nat.Prime 1232632421 := by
  apply lucas_primality 1232632421 (2 : ZMod 1232632421)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (71, 1), (868051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (71, 1), (868051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1232632421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_twentyNineAA_868051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1232632421) ^ 616316210 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1232632421) ^ 246526484 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1232632421) ^ 17361020 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1232632421) ^ 1420 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1472856311 : Nat.Prime 1472856311 := by
  apply lucas_primality 1472856311 (11 : ZMod 1472856311)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67, 1), (2198293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67, 1), (2198293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472856311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_67
      · exact prime_twentyNineAA_2198293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1472856311) ^ 736428155 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1472856311) ^ 294571262 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1472856311) ^ 21982930 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1472856311) ^ 670 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1508622361 : Nat.Prime 1508622361 := by
  apply lucas_primality 1508622361 (34 : ZMod 1508622361)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (1795979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (1795979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508622361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_1795979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 1508622361) ^ 754311180 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (34 : ZMod 1508622361) ^ 502874120 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (34 : ZMod 1508622361) ^ 301724472 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (34 : ZMod 1508622361) ^ 215517480 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (34 : ZMod 1508622361) ^ 840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1654987469 : Nat.Prime 1654987469 := by
  apply lucas_primality 1654987469 (2 : ZMod 1654987469)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (41, 1), (277, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (41, 1), (277, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654987469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_twentyNineAA_277
      · exact prime_twentyNineAA_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1654987469) ^ 827493734 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654987469) ^ 97352204 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654987469) ^ 40365548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654987469) ^ 5974684 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654987469) ^ 772276 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1733684257 : Nat.Prime 1733684257 := by
  apply lucas_primality 1733684257 (5 : ZMod 1733684257)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (2006579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (2006579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733684257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_2006579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1733684257) ^ 866842128 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1733684257) ^ 577894752 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1733684257) ^ 864 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1768515109 : Nat.Prime 1768515109 := by
  apply lucas_primality 1768515109 (2 : ZMod 1768515109)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (147376259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (147376259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1768515109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_147376259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1768515109) ^ 884257554 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768515109) ^ 589505036 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1768515109) ^ 12 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1786995227 : Nat.Prime 1786995227 := by
  apply lucas_primality 1786995227 (2 : ZMod 1786995227)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3739, 1), (238967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3739, 1), (238967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1786995227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3739
      · exact prime_twentyNineAA_238967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1786995227) ^ 893497613 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1786995227) ^ 477934 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1786995227) ^ 7478 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2192155289 : Nat.Prime 2192155289 := by
  apply lucas_primality 2192155289 (3 : ZMod 2192155289)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (274019411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (274019411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192155289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_274019411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2192155289) ^ 1096077644 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2192155289) ^ 8 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2781578783 : Nat.Prime 2781578783 := by
  apply lucas_primality 2781578783 (5 : ZMod 2781578783)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (379, 1), (46451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (379, 1), (46451, 1)] : List FactorBlock).map factorBlockValue).prod) = 2781578783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_twentyNineAA_379
      · exact prime_twentyNineAA_46451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2781578783) ^ 1390789391 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2781578783) ^ 35209858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2781578783) ^ 7339258 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2781578783) ^ 59882 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2930160707 : Nat.Prime 2930160707 := by
  apply lucas_primality 2930160707 (2 : ZMod 2930160707)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (89, 1), (1496507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (89, 1), (1496507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2930160707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_89
      · exact prime_twentyNineAA_1496507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2930160707) ^ 1465080353 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930160707) ^ 266378246 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930160707) ^ 32923154 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930160707) ^ 1958 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3381285577 : Nat.Prime 3381285577 := by
  apply lucas_primality 3381285577 (10 : ZMod 3381285577)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (140886899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (140886899, 1)] : List FactorBlock).map factorBlockValue).prod) = 3381285577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_140886899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 3381285577) ^ 1690642788 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 3381285577) ^ 1127095192 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 3381285577) ^ 24 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3691173029 : Nat.Prime 3691173029 := by
  apply lucas_primality 3691173029 (2 : ZMod 3691173029)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7823, 1), (117959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7823, 1), (117959, 1)] : List FactorBlock).map factorBlockValue).prod) = 3691173029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_7823
      · exact prime_twentyNineAA_117959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3691173029) ^ 1845586514 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691173029) ^ 471836 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691173029) ^ 31292 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3779416853 : Nat.Prime 3779416853 := by
  apply lucas_primality 3779416853 (2 : ZMod 3779416853)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (409, 1), (2310157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (409, 1), (2310157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3779416853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_409
      · exact prime_twentyNineAA_2310157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3779416853) ^ 1889708426 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3779416853) ^ 9240628 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3779416853) ^ 1636 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3914428097 : Nat.Prime 3914428097 := by
  apply lucas_primality 3914428097 (3 : ZMod 3914428097)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41, 1), (173, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41, 1), (173, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3914428097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_twentyNineAA_173
      · exact prime_twentyNineAA_8623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3914428097) ^ 1957214048 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3914428097) ^ 95473856 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3914428097) ^ 22626752 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3914428097) ^ 453952 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_4869832819 : Nat.Prime 4869832819 := by
  apply lucas_primality 4869832819 (2 : ZMod 4869832819)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (1110313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (1110313, 1)] : List FactorBlock).map factorBlockValue).prod) = 4869832819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_43
      · exact prime_twentyNineAA_1110313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4869832819) ^ 2434916409 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869832819) ^ 1623277606 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869832819) ^ 286460754 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869832819) ^ 113251926 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869832819) ^ 4386 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_5207154947 : Nat.Prime 5207154947 := by
  apply lucas_primality 5207154947 (2 : ZMod 5207154947)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (431, 1), (433, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (431, 1), (433, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) = 5207154947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_431
      · exact prime_t64_433
      · exact prime_twentyNineAA_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5207154947) ^ 2603577473 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207154947) ^ 743879278 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207154947) ^ 12081566 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207154947) ^ 12025762 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5207154947) ^ 2612722 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_5275880383 : Nat.Prime 5275880383 := by
  apply lucas_primality 5275880383 (3 : ZMod 5275880383)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (733, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (733, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) = 5275880383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_twentyNineAA_733
      · exact prime_twentyNineAA_16433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5275880383) ^ 2637940191 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5275880383) ^ 1758626794 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5275880383) ^ 72272334 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5275880383) ^ 7197654 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5275880383) ^ 321054 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_5326346873 : Nat.Prime 5326346873 := by
  apply lucas_primality 5326346873 (3 : ZMod 5326346873)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (8646667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (8646667, 1)] : List FactorBlock).map factorBlockValue).prod) = 5326346873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyNineAA_8646667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5326346873) ^ 2663173436 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5326346873) ^ 760906696 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5326346873) ^ 484213352 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5326346873) ^ 616 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_5944650379 : Nat.Prime 5944650379 := by
  apply lucas_primality 5944650379 (3 : ZMod 5944650379)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (990775063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (990775063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5944650379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_990775063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5944650379) ^ 2972325189 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5944650379) ^ 1981550126 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5944650379) ^ 6 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_6922233421 : Nat.Prime 6922233421 := by
  apply lucas_primality 6922233421 (19 : ZMod 6922233421)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (10289, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (10289, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) = 6922233421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_10289
      · exact prime_twentyNineAA_11213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 6922233421) ^ 3461116710 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 6922233421) ^ 2307411140 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 6922233421) ^ 1384446684 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 6922233421) ^ 672780 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (19 : ZMod 6922233421) ^ 617340 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_7271719699 : Nat.Prime 7271719699 := by
  apply lucas_primality 7271719699 (2 : ZMod 7271719699)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (647, 1), (3541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (647, 1), (3541, 1)] : List FactorBlock).map factorBlockValue).prod) = 7271719699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_647
      · exact prime_twentyNineAA_3541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7271719699) ^ 3635859849 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7271719699) ^ 2423906566 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7271719699) ^ 316161726 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7271719699) ^ 11239134 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7271719699) ^ 2053578 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_7526511341 : Nat.Prime 7526511341 := by
  apply lucas_primality 7526511341 (2 : ZMod 7526511341)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (376325567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (376325567, 1)] : List FactorBlock).map factorBlockValue).prod) = 7526511341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_376325567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7526511341) ^ 3763255670 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7526511341) ^ 1505302268 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7526511341) ^ 20 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_7846619701 : Nat.Prime 7846619701 := by
  apply lucas_primality 7846619701 (6 : ZMod 7846619701)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (79, 1), (331081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (79, 1), (331081, 1)] : List FactorBlock).map factorBlockValue).prod) = 7846619701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_twentyNineAA_331081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7846619701) ^ 3923309850 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7846619701) ^ 2615539900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7846619701) ^ 1569323940 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7846619701) ^ 99324300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7846619701) ^ 23700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_8211413993 : Nat.Prime 8211413993 := by
  apply lucas_primality 8211413993 (3 : ZMod 8211413993)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (21838867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (21838867, 1)] : List FactorBlock).map factorBlockValue).prod) = 8211413993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_twentyNineAA_21838867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8211413993) ^ 4105706996 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8211413993) ^ 174710936 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 8211413993) ^ 376 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_14146116343 : Nat.Prime 14146116343 := by
  apply lucas_primality 14146116343 (3 : ZMod 14146116343)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7309, 1), (322573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7309, 1), (322573, 1)] : List FactorBlock).map factorBlockValue).prod) = 14146116343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_7309
      · exact prime_twentyNineAA_322573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14146116343) ^ 7073058171 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14146116343) ^ 4715372114 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14146116343) ^ 1935438 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14146116343) ^ 43854 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_14487094841 : Nat.Prime 14487094841 := by
  apply lucas_primality 14487094841 (3 : ZMod 14487094841)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (11683141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (11683141, 1)] : List FactorBlock).map factorBlockValue).prod) = 14487094841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_twentyNineAA_11683141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14487094841) ^ 7243547420 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14487094841) ^ 2897418968 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14487094841) ^ 467325640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 14487094841) ^ 1240 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_17341436719 : Nat.Prime 17341436719 := by
  apply lucas_primality 17341436719 (6 : ZMod 17341436719)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (7468319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (7468319, 1)] : List FactorBlock).map factorBlockValue).prod) = 17341436719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_7468319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 17341436719) ^ 8670718359 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 17341436719) ^ 5780478906 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 17341436719) ^ 403289226 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 17341436719) ^ 2322 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_18075707413 : Nat.Prime 18075707413 := by
  apply lucas_primality 18075707413 (5 : ZMod 18075707413)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (421, 1), (73019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (421, 1), (73019, 1)] : List FactorBlock).map factorBlockValue).prod) = 18075707413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_421
      · exact prime_twentyNineAA_73019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18075707413) ^ 9037853706 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18075707413) ^ 6025235804 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18075707413) ^ 2582243916 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18075707413) ^ 42935172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18075707413) ^ 247548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_19817048567 : Nat.Prime 19817048567 := by
  apply lucas_primality 19817048567 (5 : ZMod 19817048567)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1039, 1), (1362371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1039, 1), (1362371, 1)] : List FactorBlock).map factorBlockValue).prod) = 19817048567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_1039
      · exact prime_twentyNineAA_1362371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19817048567) ^ 9908524283 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19817048567) ^ 2831006938 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19817048567) ^ 19073194 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19817048567) ^ 14546 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20273080687 : Nat.Prime 20273080687 := by
  apply lucas_primality 20273080687 (3 : ZMod 20273080687)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (179, 1), (1110367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (179, 1), (1110367, 1)] : List FactorBlock).map factorBlockValue).prod) = 20273080687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_179
      · exact prime_twentyNineAA_1110367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20273080687) ^ 10136540343 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20273080687) ^ 6757693562 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20273080687) ^ 1192534158 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20273080687) ^ 113257434 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20273080687) ^ 18258 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20355353261 : Nat.Prime 20355353261 := by
  apply lucas_primality 20355353261 (2 : ZMod 20355353261)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 2), (83, 1), (101341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 2), (83, 1), (101341, 1)] : List FactorBlock).map factorBlockValue).prod) = 20355353261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_83
      · exact prime_twentyNineAA_101341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20355353261) ^ 10177676630 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20355353261) ^ 4071070652 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20355353261) ^ 1850486660 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20355353261) ^ 245245220 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20355353261) ^ 200860 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20437512653 : Nat.Prime 20437512653 := by
  apply lucas_primality 20437512653 (2 : ZMod 20437512653)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8831, 1), (578573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8831, 1), (578573, 1)] : List FactorBlock).map factorBlockValue).prod) = 20437512653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_8831
      · exact prime_twentyNineAA_578573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20437512653) ^ 10218756326 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20437512653) ^ 2314292 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20437512653) ^ 35324 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20758822871 : Nat.Prime 20758822871 := by
  apply lucas_primality 20758822871 (13 : ZMod 20758822871)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (419, 1), (1223, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (419, 1), (1223, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 20758822871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_419
      · exact prime_twentyNineAA_1223
      · exact prime_twentyNineAA_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 20758822871) ^ 10379411435 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 20758822871) ^ 4151764574 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 20758822871) ^ 49543730 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 20758822871) ^ 16973690 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 20758822871) ^ 5124370 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_21964618141 : Nat.Prime 21964618141 := by
  apply lucas_primality 21964618141 (10 : ZMod 21964618141)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (73, 1), (463, 1), (10831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (73, 1), (463, 1), (10831, 1)] : List FactorBlock).map factorBlockValue).prod) = 21964618141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_73
      · exact prime_twentyNineAA_463
      · exact prime_twentyNineAA_10831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21964618141) ^ 10982309070 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 21964618141) ^ 7321539380 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 21964618141) ^ 4392923628 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 21964618141) ^ 300885180 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 21964618141) ^ 47439780 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 21964618141) ^ 2027940 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_24602152439 : Nat.Prime 24602152439 := by
  apply lucas_primality 24602152439 (7 : ZMod 24602152439)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (313, 1), (39300563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (313, 1), (39300563, 1)] : List FactorBlock).map factorBlockValue).prod) = 24602152439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_313
      · exact prime_twentyNineAA_39300563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 24602152439) ^ 12301076219 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 24602152439) ^ 78601126 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 24602152439) ^ 626 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_26262245357 : Nat.Prime 26262245357 := by
  apply lucas_primality 26262245357 (2 : ZMod 26262245357)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (152687473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (152687473, 1)] : List FactorBlock).map factorBlockValue).prod) = 26262245357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_twentyNineAA_152687473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26262245357) ^ 13131122678 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26262245357) ^ 610749892 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26262245357) ^ 172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_26934616883 : Nat.Prime 26934616883 := by
  apply lucas_primality 26934616883 (2 : ZMod 26934616883)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5813, 1), (2316757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5813, 1), (2316757, 1)] : List FactorBlock).map factorBlockValue).prod) = 26934616883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_5813
      · exact prime_twentyNineAA_2316757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26934616883) ^ 13467308441 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26934616883) ^ 4633514 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26934616883) ^ 11626 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_30398254097 : Nat.Prime 30398254097 := by
  apply lucas_primality 30398254097 (3 : ZMod 30398254097)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (5297, 1), (51239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (5297, 1), (51239, 1)] : List FactorBlock).map factorBlockValue).prod) = 30398254097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_5297
      · exact prime_twentyNineAA_51239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30398254097) ^ 15199127048 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30398254097) ^ 4342607728 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30398254097) ^ 5738768 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 30398254097) ^ 593264 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_31655282299 : Nat.Prime 31655282299 := by
  apply lucas_primality 31655282299 (3 : ZMod 31655282299)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5275880383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5275880383, 1)] : List FactorBlock).map factorBlockValue).prod) = 31655282299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_5275880383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31655282299) ^ 15827641149 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31655282299) ^ 10551760766 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 31655282299) ^ 6 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_34252816553 : Nat.Prime 34252816553 := by
  apply lucas_primality 34252816553 (3 : ZMod 34252816553)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (20719, 1), (206651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (20719, 1), (206651, 1)] : List FactorBlock).map factorBlockValue).prod) = 34252816553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_20719
      · exact prime_twentyNineAA_206651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 34252816553) ^ 17126408276 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34252816553) ^ 1653208 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 34252816553) ^ 165752 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_39278214779 : Nat.Prime 39278214779 := by
  apply lucas_primality 39278214779 (6 : ZMod 39278214779)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (93967021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (93967021, 1)] : List FactorBlock).map factorBlockValue).prod) = 39278214779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_twentyNineAA_93967021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 39278214779) ^ 19639107389 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39278214779) ^ 3570746798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39278214779) ^ 2067274462 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39278214779) ^ 418 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_40710706523 : Nat.Prime 40710706523 := by
  apply lucas_primality 40710706523 (2 : ZMod 40710706523)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20355353261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20355353261, 1)] : List FactorBlock).map factorBlockValue).prod) = 40710706523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_20355353261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 40710706523) ^ 20355353261 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40710706523) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_41681616049 : Nat.Prime 41681616049 := by
  apply lucas_primality 41681616049 (7 : ZMod 41681616049)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (233, 1), (54013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (233, 1), (54013, 1)] : List FactorBlock).map factorBlockValue).prod) = 41681616049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_233
      · exact prime_twentyNineAA_54013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 41681616049) ^ 20840808024 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 41681616049) ^ 13893872016 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 41681616049) ^ 1812244176 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 41681616049) ^ 178891056 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 41681616049) ^ 771696 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_46913371289 : Nat.Prime 46913371289 := by
  apply lucas_primality 46913371289 (3 : ZMod 46913371289)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41, 1), (463, 1), (44131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41, 1), (463, 1), (44131, 1)] : List FactorBlock).map factorBlockValue).prod) = 46913371289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_41
      · exact prime_twentyNineAA_463
      · exact prime_twentyNineAA_44131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46913371289) ^ 23456685644 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46913371289) ^ 6701910184 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46913371289) ^ 1144228568 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46913371289) ^ 101324776 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46913371289) ^ 1063048 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_47136331573 : Nat.Prime 47136331573 := by
  apply lucas_primality 47136331573 (2 : ZMod 47136331573)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (379, 1), (942199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (379, 1), (942199, 1)] : List FactorBlock).map factorBlockValue).prod) = 47136331573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_379
      · exact prime_twentyNineAA_942199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47136331573) ^ 23568165786 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47136331573) ^ 15712110524 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47136331573) ^ 4285121052 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47136331573) ^ 124370268 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47136331573) ^ 50028 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_48735048319 : Nat.Prime 48735048319 := by
  apply lucas_primality 48735048319 (6 : ZMod 48735048319)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (373, 1), (811, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (373, 1), (811, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) = 48735048319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_373
      · exact prime_twentyNineAA_811
      · exact prime_twentyNineAA_2441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 48735048319) ^ 24367524159 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 48735048319) ^ 16245016106 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 48735048319) ^ 4430458938 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 48735048319) ^ 130656966 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 48735048319) ^ 60092538 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 48735048319) ^ 19965198 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_74121292807 : Nat.Prime 74121292807 := by
  apply lucas_primality 74121292807 (6 : ZMod 74121292807)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (103, 1), (573863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (103, 1), (573863, 1)] : List FactorBlock).map factorBlockValue).prod) = 74121292807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_t64_103
      · exact prime_twentyNineAA_573863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 74121292807) ^ 37060646403 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 74121292807) ^ 24707097602 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 74121292807) ^ 6738299346 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 74121292807) ^ 3901120674 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 74121292807) ^ 719624202 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 74121292807) ^ 129162 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_86058616961 : Nat.Prime 86058616961 := by
  apply lucas_primality 86058616961 (3 : ZMod 86058616961)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (1381, 1), (97369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (1381, 1), (97369, 1)] : List FactorBlock).map factorBlockValue).prod) = 86058616961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_1381
      · exact prime_twentyNineAA_97369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86058616961) ^ 43029308480 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86058616961) ^ 17211723392 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86058616961) ^ 62316160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 86058616961) ^ 883840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_92390778239 : Nat.Prime 92390778239 := by
  apply lucas_primality 92390778239 (7 : ZMod 92390778239)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (383, 1), (138797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (383, 1), (138797, 1)] : List FactorBlock).map factorBlockValue).prod) = 92390778239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_79
      · exact prime_t64_383
      · exact prime_twentyNineAA_138797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 92390778239) ^ 46195389119 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 92390778239) ^ 8399161658 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 92390778239) ^ 1169503522 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 92390778239) ^ 241229186 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 92390778239) ^ 665654 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_99840294209 : Nat.Prime 99840294209 := by
  apply lucas_primality 99840294209 (3 : ZMod 99840294209)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (53, 1), (727, 1), (40487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (53, 1), (727, 1), (40487, 1)] : List FactorBlock).map factorBlockValue).prod) = 99840294209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentyNineAA_727
      · exact prime_twentyNineAA_40487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 99840294209) ^ 49920147104 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 99840294209) ^ 1883779136 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 99840294209) ^ 137331904 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 99840294209) ^ 2465984 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_99937845391 : Nat.Prime 99937845391 := by
  apply lucas_primality 99937845391 (13 : ZMod 99937845391)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (337, 1), (9885049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (337, 1), (9885049, 1)] : List FactorBlock).map factorBlockValue).prod) = 99937845391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_337
      · exact prime_twentyNineAA_9885049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 99937845391) ^ 49968922695 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99937845391) ^ 33312615130 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99937845391) ^ 19987569078 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99937845391) ^ 296551470 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99937845391) ^ 10110 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_102240442723 : Nat.Prime 102240442723 := by
  apply lucas_primality 102240442723 (2 : ZMod 102240442723)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (9161, 1), (169097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (9161, 1), (169097, 1)] : List FactorBlock).map factorBlockValue).prod) = 102240442723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_9161
      · exact prime_twentyNineAA_169097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102240442723) ^ 51120221361 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102240442723) ^ 34080147574 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102240442723) ^ 9294585702 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102240442723) ^ 11160402 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102240442723) ^ 604626 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_103350955361 : Nat.Prime 103350955361 := by
  apply lucas_primality 103350955361 (3 : ZMod 103350955361)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11551, 1), (55921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11551, 1), (55921, 1)] : List FactorBlock).map factorBlockValue).prod) = 103350955361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_11551
      · exact prime_twentyNineAA_55921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103350955361) ^ 51675477680 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103350955361) ^ 20670191072 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103350955361) ^ 8947360 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103350955361) ^ 1848160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_107737082639 : Nat.Prime 107737082639 := by
  apply lucas_primality 107737082639 (7 : ZMod 107737082639)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (317, 1), (3615581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (317, 1), (3615581, 1)] : List FactorBlock).map factorBlockValue).prod) = 107737082639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_t64_317
      · exact prime_twentyNineAA_3615581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 107737082639) ^ 53868541319 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 107737082639) ^ 2292278354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 107737082639) ^ 339864614 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 107737082639) ^ 29798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_141740066651 : Nat.Prime 141740066651 := by
  apply lucas_primality 141740066651 (2 : ZMod 141740066651)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (13, 1), (61, 1), (510683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (13, 1), (61, 1), (510683, 1)] : List FactorBlock).map factorBlockValue).prod) = 141740066651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_61
      · exact prime_twentyNineAA_510683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141740066651) ^ 70870033325 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141740066651) ^ 28348013330 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141740066651) ^ 20248580950 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141740066651) ^ 10903082050 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141740066651) ^ 2323607650 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141740066651) ^ 277550 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_180543740843 : Nat.Prime 180543740843 := by
  apply lucas_primality 180543740843 (2 : ZMod 180543740843)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30109, 1), (2998169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30109, 1), (2998169, 1)] : List FactorBlock).map factorBlockValue).prod) = 180543740843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_30109
      · exact prime_twentyNineAA_2998169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 180543740843) ^ 90271870421 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 180543740843) ^ 5996338 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 180543740843) ^ 60218 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_327297336473 : Nat.Prime 327297336473 := by
  apply lucas_primality 327297336473 (3 : ZMod 327297336473)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (121571, 1), (336529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (121571, 1), (336529, 1)] : List FactorBlock).map factorBlockValue).prod) = 327297336473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_121571
      · exact prime_twentyNineAA_336529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 327297336473) ^ 163648668236 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 327297336473) ^ 2692232 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 327297336473) ^ 972568 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_384219483719 : Nat.Prime 384219483719 := by
  apply lucas_primality 384219483719 (7 : ZMod 384219483719)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61469, 1), (446473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61469, 1), (446473, 1)] : List FactorBlock).map factorBlockValue).prod) = 384219483719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_61469
      · exact prime_twentyNineAA_446473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 384219483719) ^ 192109741859 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 384219483719) ^ 54888497674 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 384219483719) ^ 6250622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 384219483719) ^ 860566 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_416816160491 : Nat.Prime 416816160491 := by
  apply lucas_primality 416816160491 (2 : ZMod 416816160491)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41681616049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41681616049, 1)] : List FactorBlock).map factorBlockValue).prod) = 416816160491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_41681616049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 416816160491) ^ 208408080245 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 416816160491) ^ 83363232098 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 416816160491) ^ 10 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_421484635097 : Nat.Prime 421484635097 := by
  apply lucas_primality 421484635097 (5 : ZMod 421484635097)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (7526511341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (7526511341, 1)] : List FactorBlock).map factorBlockValue).prod) = 421484635097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_7526511341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 421484635097) ^ 210742317548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 421484635097) ^ 60212090728 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 421484635097) ^ 56 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_425575557359 : Nat.Prime 425575557359 := by
  apply lucas_primality 425575557359 (7 : ZMod 425575557359)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (30398254097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (30398254097, 1)] : List FactorBlock).map factorBlockValue).prod) = 425575557359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_30398254097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 425575557359) ^ 212787778679 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 425575557359) ^ 60796508194 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 425575557359) ^ 14 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_466799876303 : Nat.Prime 466799876303 := by
  apply lucas_primality 466799876303 (5 : ZMod 466799876303)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (179, 1), (12659323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (179, 1), (12659323, 1)] : List FactorBlock).map factorBlockValue).prod) = 466799876303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_103
      · exact prime_t64_179
      · exact prime_twentyNineAA_12659323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 466799876303) ^ 233399938151 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 466799876303) ^ 4532037634 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 466799876303) ^ 2607820538 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 466799876303) ^ 36874 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_565844653721 : Nat.Prime 565844653721 := by
  apply lucas_primality 565844653721 (3 : ZMod 565844653721)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (14146116343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (14146116343, 1)] : List FactorBlock).map factorBlockValue).prod) = 565844653721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_14146116343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 565844653721) ^ 282922326860 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 565844653721) ^ 113168930744 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 565844653721) ^ 40 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_594511457011 : Nat.Prime 594511457011 := by
  apply lucas_primality 594511457011 (3 : ZMod 594511457011)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19817048567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19817048567, 1)] : List FactorBlock).map factorBlockValue).prod) = 594511457011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_19817048567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 594511457011) ^ 297255728505 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 594511457011) ^ 198170485670 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 594511457011) ^ 118902291402 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 594511457011) ^ 30 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_626550481157 : Nat.Prime 626550481157 := by
  apply lucas_primality 626550481157 (2 : ZMod 626550481157)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (3083, 1), (1373159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (3083, 1), (1373159, 1)] : List FactorBlock).map factorBlockValue).prod) = 626550481157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_twentyNineAA_3083
      · exact prime_twentyNineAA_1373159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 626550481157) ^ 313275240578 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 626550481157) ^ 16933796788 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 626550481157) ^ 203227532 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 626550481157) ^ 456284 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_640831669007 : Nat.Prime 640831669007 := by
  apply lucas_primality 640831669007 (5 : ZMod 640831669007)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (83, 1), (193, 1), (349, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (83, 1), (193, 1), (349, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) = 640831669007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_83
      · exact prime_t64_193
      · exact prime_t64_349
      · exact prime_twentyNineAA_1549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 640831669007) ^ 320415834503 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 640831669007) ^ 17319774838 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 640831669007) ^ 7720863482 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 640831669007) ^ 3320371342 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 640831669007) ^ 1836193894 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 640831669007) ^ 413706694 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_730184980181 : Nat.Prime 730184980181 := by
  apply lucas_primality 730184980181 (2 : ZMod 730184980181)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (89, 1), (14145389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (89, 1), (14145389, 1)] : List FactorBlock).map factorBlockValue).prod) = 730184980181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_t64_89
      · exact prime_twentyNineAA_14145389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 730184980181) ^ 365092490090 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 730184980181) ^ 146036996036 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 730184980181) ^ 25178792420 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 730184980181) ^ 8204325620 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 730184980181) ^ 51620 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_932511659537 : Nat.Prime 932511659537 := by
  apply lucas_primality 932511659537 (3 : ZMod 932511659537)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7019, 1), (8303459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7019, 1), (8303459, 1)] : List FactorBlock).map factorBlockValue).prod) = 932511659537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_7019
      · exact prime_twentyNineAA_8303459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 932511659537) ^ 466255829768 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 932511659537) ^ 132855344 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 932511659537) ^ 112304 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1082447922239 : Nat.Prime 1082447922239 := by
  apply lucas_primality 1082447922239 (13 : ZMod 1082447922239)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (173, 1), (229, 1), (431, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (173, 1), (229, 1), (431, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1082447922239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_twentyNineAA_173
      · exact prime_t64_229
      · exact prime_t64_431
      · exact prime_t64_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1082447922239) ^ 541223961119 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1082447922239) ^ 37325790422 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1082447922239) ^ 6256924406 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1082447922239) ^ 4726846822 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1082447922239) ^ 2511480098 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1082447922239) ^ 990345766 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1531609041593 : Nat.Prime 1531609041593 := by
  apply lucas_primality 1531609041593 (3 : ZMod 1531609041593)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (14551, 1), (1879607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (14551, 1), (1879607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1531609041593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_14551
      · exact prime_twentyNineAA_1879607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1531609041593) ^ 765804520796 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531609041593) ^ 218801291656 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531609041593) ^ 105257992 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1531609041593) ^ 814856 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2054546302339 : Nat.Prime 2054546302339 := by
  apply lucas_primality 2054546302339 (2 : ZMod 2054546302339)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (2273, 1), (389273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (2273, 1), (389273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2054546302339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_2273
      · exact prime_twentyNineAA_389273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2054546302339) ^ 1027273151169 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054546302339) ^ 684848767446 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054546302339) ^ 47780146566 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054546302339) ^ 903891906 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2054546302339) ^ 5277906 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2164895844479 : Nat.Prime 2164895844479 := by
  apply lucas_primality 2164895844479 (7 : ZMod 2164895844479)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1082447922239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1082447922239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2164895844479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_1082447922239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 2164895844479) ^ 1082447922239 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2164895844479) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2990860705043 : Nat.Prime 2990860705043 := by
  apply lucas_primality 2990860705043 (2 : ZMod 2990860705043)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (31, 1), (107, 1), (971, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (31, 1), (107, 1), (971, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) = 2990860705043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_31
      · exact prime_t64_107
      · exact prime_twentyNineAA_971
      · exact prime_twentyNineAA_3491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2990860705043) ^ 1495430352521 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 427265815006 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 157413721318 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 96479377582 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 27951969206 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 3080186102 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2990860705043) ^ 856734662 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3410790793159 : Nat.Prime 3410790793159 := by
  apply lucas_primality 3410790793159 (6 : ZMod 3410790793159)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (1027965881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (1027965881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3410790793159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_79
      · exact prime_twentyNineAA_1027965881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3410790793159) ^ 1705395396579 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3410790793159) ^ 1136930264386 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3410790793159) ^ 487255827594 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3410790793159) ^ 43174567002 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3410790793159) ^ 3318 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_4219943201143 : Nat.Prime 4219943201143 := by
  apply lucas_primality 4219943201143 (3 : ZMod 4219943201143)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (107, 1), (9854753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (107, 1), (9854753, 1)] : List FactorBlock).map factorBlockValue).prod) = 4219943201143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_107
      · exact prime_twentyNineAA_9854753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4219943201143) ^ 2109971600571 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219943201143) ^ 1406647733714 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219943201143) ^ 183475791354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219943201143) ^ 145515282798 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219943201143) ^ 39438721506 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4219943201143) ^ 428214 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_5777399706977 : Nat.Prime 5777399706977 := by
  apply lucas_primality 5777399706977 (3 : ZMod 5777399706977)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (180543740843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (180543740843, 1)] : List FactorBlock).map factorBlockValue).prod) = 5777399706977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_180543740843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5777399706977) ^ 2888699853488 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5777399706977) ^ 32 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_6141810816871 : Nat.Prime 6141810816871 := by
  apply lucas_primality 6141810816871 (3 : ZMod 6141810816871)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (139, 1), (1472856311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (139, 1), (1472856311, 1)] : List FactorBlock).map factorBlockValue).prod) = 6141810816871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_139
      · exact prime_twentyNineAA_1472856311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6141810816871) ^ 3070905408435 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6141810816871) ^ 2047270272290 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6141810816871) ^ 1228362163374 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6141810816871) ^ 44185689330 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6141810816871) ^ 4170 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_6625874622011 : Nat.Prime 6625874622011 := by
  apply lucas_primality 6625874622011 (2 : ZMod 6625874622011)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (197, 1), (1301, 1), (369319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (197, 1), (1301, 1), (369319, 1)] : List FactorBlock).map factorBlockValue).prod) = 6625874622011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_197
      · exact prime_twentyNineAA_1301
      · exact prime_twentyNineAA_369319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6625874622011) ^ 3312937311005 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625874622011) ^ 1325174924402 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625874622011) ^ 946553517430 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625874622011) ^ 33633881330 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625874622011) ^ 5092909010 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625874622011) ^ 17940790 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_10318483017383 : Nat.Prime 10318483017383 := by
  apply lucas_primality 10318483017383 (5 : ZMod 10318483017383)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (92737, 1), (159407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (92737, 1), (159407, 1)] : List FactorBlock).map factorBlockValue).prod) = 10318483017383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_349
      · exact prime_twentyNineAA_92737
      · exact prime_twentyNineAA_159407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10318483017383) ^ 5159241508691 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10318483017383) ^ 29565853918 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10318483017383) ^ 111266086 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 10318483017383) ^ 64730426 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_13431377838839 : Nat.Prime 13431377838839 := by
  apply lucas_primality 13431377838839 (7 : ZMod 13431377838839)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (656479, 1), (10229861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (656479, 1), (10229861, 1)] : List FactorBlock).map factorBlockValue).prod) = 13431377838839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_656479
      · exact prime_twentyNineAA_10229861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 13431377838839) ^ 6715688919419 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 13431377838839) ^ 20459722 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 13431377838839) ^ 1312958 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_14834747193983 : Nat.Prime 14834747193983 := by
  apply lucas_primality 14834747193983 (5 : ZMod 14834747193983)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4057, 1), (79490881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4057, 1), (79490881, 1)] : List FactorBlock).map factorBlockValue).prod) = 14834747193983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyNineAA_4057
      · exact prime_twentyNineAA_79490881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14834747193983) ^ 7417373596991 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14834747193983) ^ 644989008434 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14834747193983) ^ 3656580526 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14834747193983) ^ 186622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_33833725982479 : Nat.Prime 33833725982479 := by
  apply lucas_primality 33833725982479 (3 : ZMod 33833725982479)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (626550481157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (626550481157, 1)] : List FactorBlock).map factorBlockValue).prod) = 33833725982479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_626550481157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33833725982479) ^ 16916862991239 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33833725982479) ^ 11277908660826 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33833725982479) ^ 54 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_40929489517909 : Nat.Prime 40929489517909 := by
  apply lucas_primality 40929489517909 (6 : ZMod 40929489517909)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3410790793159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3410790793159, 1)] : List FactorBlock).map factorBlockValue).prod) = 40929489517909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_3410790793159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 40929489517909) ^ 20464744758954 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 40929489517909) ^ 13643163172636 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 40929489517909) ^ 12 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_61951772236997 : Nat.Prime 61951772236997 := by
  apply lucas_primality 61951772236997 (2 : ZMod 61951772236997)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (137341, 1), (4903043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (137341, 1), (4903043, 1)] : List FactorBlock).map factorBlockValue).prod) = 61951772236997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyNineAA_137341
      · exact prime_twentyNineAA_4903043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61951772236997) ^ 30975886118498 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 61951772236997) ^ 2693555314652 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 61951772236997) ^ 451079956 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 61951772236997) ^ 12635372 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_62276456384551 : Nat.Prime 62276456384551 := by
  apply lucas_primality 62276456384551 (3 : ZMod 62276456384551)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (251, 1), (491, 1), (124771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (251, 1), (491, 1), (124771, 1)] : List FactorBlock).map factorBlockValue).prod) = 62276456384551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_251
      · exact prime_t64_491
      · exact prime_twentyNineAA_124771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62276456384551) ^ 31138228192275 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62276456384551) ^ 20758818794850 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62276456384551) ^ 12455291276910 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62276456384551) ^ 248113372050 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62276456384551) ^ 126835960050 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 62276456384551) ^ 499126050 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_71848807586701 : Nat.Prime 71848807586701 := by
  apply lucas_primality 71848807586701 (6 : ZMod 71848807586701)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (61, 1), (4391, 1), (894139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (61, 1), (4391, 1), (894139, 1)] : List FactorBlock).map factorBlockValue).prod) = 71848807586701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_61
      · exact prime_twentyNineAA_4391
      · exact prime_twentyNineAA_894139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 71848807586701) ^ 35924403793350 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 71848807586701) ^ 23949602528900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 71848807586701) ^ 14369761517340 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 71848807586701) ^ 1177849304700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 71848807586701) ^ 16362743700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 71848807586701) ^ 80355300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_85198718428247 : Nat.Prime 85198718428247 := by
  apply lucas_primality 85198718428247 (7 : ZMod 85198718428247)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (647, 1), (582666893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (647, 1), (582666893, 1)] : List FactorBlock).map factorBlockValue).prod) = 85198718428247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_113
      · exact prime_t64_647
      · exact prime_twentyNineAA_582666893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 85198718428247) ^ 42599359214123 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 85198718428247) ^ 753970959542 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 85198718428247) ^ 131682717818 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 85198718428247) ^ 146222 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_90197792637923 : Nat.Prime 90197792637923 := by
  apply lucas_primality 90197792637923 (2 : ZMod 90197792637923)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (461, 1), (1693, 1), (57784057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (461, 1), (1693, 1), (57784057, 1)] : List FactorBlock).map factorBlockValue).prod) = 90197792637923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_461
      · exact prime_twentyNineAA_1693
      · exact prime_twentyNineAA_57784057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90197792637923) ^ 45098896318961 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 90197792637923) ^ 195656817002 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 90197792637923) ^ 53276900554 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 90197792637923) ^ 1560946 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_91247008889671 : Nat.Prime 91247008889671 := by
  apply lucas_primality 91247008889671 (3 : ZMod 91247008889671)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (971, 1), (8317, 1), (376627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (971, 1), (8317, 1), (376627, 1)] : List FactorBlock).map factorBlockValue).prod) = 91247008889671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_971
      · exact prime_twentyNineAA_8317
      · exact prime_twentyNineAA_376627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 91247008889671) ^ 45623504444835 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91247008889671) ^ 30415669629890 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91247008889671) ^ 18249401777934 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91247008889671) ^ 93972202770 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91247008889671) ^ 10971144510 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91247008889671) ^ 242274210 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_99666316795559 : Nat.Prime 99666316795559 := by
  apply lucas_primality 99666316795559 (13 : ZMod 99666316795559)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (313, 1), (6922233421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (313, 1), (6922233421, 1)] : List FactorBlock).map factorBlockValue).prod) = 99666316795559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyNineAA_313
      · exact prime_twentyNineAA_6922233421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 99666316795559) ^ 49833158397779 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99666316795559) ^ 4333318121546 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99666316795559) ^ 318422737366 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 99666316795559) ^ 14398 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_119281390651783 : Nat.Prime 119281390651783 := by
  apply lucas_primality 119281390651783 (3 : ZMod 119281390651783)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (32429, 1), (204346231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (32429, 1), (204346231, 1)] : List FactorBlock).map factorBlockValue).prod) = 119281390651783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_32429
      · exact prime_twentyNineAA_204346231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119281390651783) ^ 59640695325891 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281390651783) ^ 39760463550594 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281390651783) ^ 3678232158 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 119281390651783) ^ 583722 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_141867430349263 : Nat.Prime 141867430349263 := by
  apply lucas_primality 141867430349263 (5 : ZMod 141867430349263)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (743, 1), (600436063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (743, 1), (600436063, 1)] : List FactorBlock).map factorBlockValue).prod) = 141867430349263 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_twentyNineAA_743
      · exact prime_twentyNineAA_600436063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141867430349263) ^ 70933715174631 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141867430349263) ^ 47289143449754 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141867430349263) ^ 2676743968854 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141867430349263) ^ 190938668034 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141867430349263) ^ 236274 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_185626757071159 : Nat.Prime 185626757071159 := by
  apply lucas_primality 185626757071159 (3 : ZMod 185626757071159)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (73, 1), (54443, 1), (598799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (73, 1), (54443, 1), (598799, 1)] : List FactorBlock).map factorBlockValue).prod) = 185626757071159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_73
      · exact prime_twentyNineAA_54443
      · exact prime_twentyNineAA_598799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185626757071159) ^ 92813378535579 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 185626757071159) ^ 61875585690386 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 185626757071159) ^ 14278981313166 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 185626757071159) ^ 2542832288646 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 185626757071159) ^ 3409561506 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 185626757071159) ^ 309998442 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_227469550795843 : Nat.Prime 227469550795843 := by
  apply lucas_primality 227469550795843 (2 : ZMod 227469550795843)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (565844653721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (565844653721, 1)] : List FactorBlock).map factorBlockValue).prod) = 227469550795843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_twentyNineAA_565844653721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 227469550795843) ^ 113734775397921 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 227469550795843) ^ 75823183598614 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 227469550795843) ^ 3395067922326 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 227469550795843) ^ 402 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_282745919254433 : Nat.Prime 282745919254433 := by
  apply lucas_primality 282745919254433 (3 : ZMod 282745919254433)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (176327, 1), (50110363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (176327, 1), (50110363, 1)] : List FactorBlock).map factorBlockValue).prod) = 282745919254433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_176327
      · exact prime_twentyNineAA_50110363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 282745919254433) ^ 141372959627216 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 282745919254433) ^ 1603531616 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 282745919254433) ^ 5642464 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_286403419834859 : Nat.Prime 286403419834859 := by
  apply lucas_primality 286403419834859 (2 : ZMod 286403419834859)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (2131, 1), (74089637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (2131, 1), (74089637, 1)] : List FactorBlock).map factorBlockValue).prod) = 286403419834859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_907
      · exact prime_twentyNineAA_2131
      · exact prime_twentyNineAA_74089637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 286403419834859) ^ 143201709917429 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 286403419834859) ^ 315770032894 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 286403419834859) ^ 134398601518 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 286403419834859) ^ 3865634 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_287122627684129 : Nat.Prime 287122627684129 := by
  apply lucas_primality 287122627684129 (7 : ZMod 287122627684129)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2990860705043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2990860705043, 1)] : List FactorBlock).map factorBlockValue).prod) = 287122627684129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_2990860705043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 287122627684129) ^ 143561313842064 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 287122627684129) ^ 95707542561376 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 287122627684129) ^ 96 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_288005176415699 : Nat.Prime 288005176415699 := by
  apply lucas_primality 288005176415699 (2 : ZMod 288005176415699)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (234653, 1), (87669019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (234653, 1), (87669019, 1)] : List FactorBlock).map factorBlockValue).prod) = 288005176415699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_234653
      · exact prime_twentyNineAA_87669019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 288005176415699) ^ 144002588207849 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 288005176415699) ^ 41143596630814 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 288005176415699) ^ 1227366266 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 288005176415699) ^ 3285142 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_290516063034469 : Nat.Prime 290516063034469 := by
  apply lucas_primality 290516063034469 (2 : ZMod 290516063034469)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (761, 1), (43517, 1), (731047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (761, 1), (43517, 1), (731047, 1)] : List FactorBlock).map factorBlockValue).prod) = 290516063034469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_761
      · exact prime_twentyNineAA_43517
      · exact prime_twentyNineAA_731047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 290516063034469) ^ 145258031517234 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 290516063034469) ^ 96838687678156 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 290516063034469) ^ 381755667588 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 290516063034469) ^ 6675921204 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 290516063034469) ^ 397397244 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_410980734244127 : Nat.Prime 410980734244127 := by
  apply lucas_primality 410980734244127 (5 : ZMod 410980734244127)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (416816160491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (416816160491, 1)] : List FactorBlock).map factorBlockValue).prod) = 410980734244127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_29
      · exact prime_twentyNineAA_416816160491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 410980734244127) ^ 205490367122063 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 410980734244127) ^ 24175337308478 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 410980734244127) ^ 14171749456694 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 410980734244127) ^ 986 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_426632743730209 : Nat.Prime 426632743730209 := by
  apply lucas_primality 426632743730209 (17 : ZMod 426632743730209)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (43, 1), (103350955361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (43, 1), (103350955361, 1)] : List FactorBlock).map factorBlockValue).prod) = 426632743730209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_103350955361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 426632743730209) ^ 213316371865104 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 426632743730209) ^ 142210914576736 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 426632743730209) ^ 9921691714656 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 426632743730209) ^ 4128 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_445327081993063 : Nat.Prime 445327081993063 := by
  apply lucas_primality 445327081993063 (3 : ZMod 445327081993063)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (466799876303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (466799876303, 1)] : List FactorBlock).map factorBlockValue).prod) = 445327081993063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_53
      · exact prime_twentyNineAA_466799876303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 445327081993063) ^ 222663540996531 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 445327081993063) ^ 148442360664354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 445327081993063) ^ 8402397773454 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 445327081993063) ^ 954 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_550517086187513 : Nat.Prime 550517086187513 := by
  apply lucas_primality 550517086187513 (3 : ZMod 550517086187513)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1321, 1), (2371, 1), (21970829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1321, 1), (2371, 1), (21970829, 1)] : List FactorBlock).map factorBlockValue).prod) = 550517086187513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_1321
      · exact prime_twentyNineAA_2371
      · exact prime_twentyNineAA_21970829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550517086187513) ^ 275258543093756 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 550517086187513) ^ 416742684472 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 550517086187513) ^ 232187720872 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 550517086187513) ^ 25056728 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_741737359699151 : Nat.Prime 741737359699151 := by
  apply lucas_primality 741737359699151 (7 : ZMod 741737359699151)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (14834747193983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (14834747193983, 1)] : List FactorBlock).map factorBlockValue).prod) = 741737359699151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_14834747193983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 741737359699151) ^ 370868679849575 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 741737359699151) ^ 148347471939830 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 741737359699151) ^ 50 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1276786868332813 : Nat.Prime 1276786868332813 := by
  apply lucas_primality 1276786868332813 (11 : ZMod 1276786868332813)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (1063, 1), (5501, 1), (204443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (1063, 1), (5501, 1), (204443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276786868332813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_twentyNineAA_1063
      · exact prime_twentyNineAA_5501
      · exact prime_twentyNineAA_204443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1276786868332813) ^ 638393434166406 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1276786868332813) ^ 425595622777604 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1276786868332813) ^ 14345919868908 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1276786868332813) ^ 1201116527124 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1276786868332813) ^ 232100866812 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1276786868332813) ^ 6245197284 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1492805092926899 : Nat.Prime 1492805092926899 := by
  apply lucas_primality 1492805092926899 (2 : ZMod 1492805092926899)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6359, 1), (29297, 1), (4006463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6359, 1), (29297, 1), (4006463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492805092926899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_6359
      · exact prime_twentyNineAA_29297
      · exact prime_twentyNineAA_4006463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1492805092926899) ^ 746402546463449 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492805092926899) ^ 234754693022 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492805092926899) ^ 50954196434 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492805092926899) ^ 372599246 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1583713125341279 : Nat.Prime 1583713125341279 := by
  apply lucas_primality 1583713125341279 (7 : ZMod 1583713125341279)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (19423, 1), (44949299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (19423, 1), (44949299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583713125341279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_907
      · exact prime_twentyNineAA_19423
      · exact prime_twentyNineAA_44949299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1583713125341279) ^ 791856562670639 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1583713125341279) ^ 1746100468954 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1583713125341279) ^ 81538028386 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1583713125341279) ^ 35233322 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2158321061215577 : Nat.Prime 2158321061215577 := by
  apply lucas_primality 2158321061215577 (3 : ZMod 2158321061215577)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (421, 1), (640831669007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (421, 1), (640831669007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2158321061215577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_421
      · exact prime_twentyNineAA_640831669007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2158321061215577) ^ 1079160530607788 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2158321061215577) ^ 5126653352056 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2158321061215577) ^ 3368 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2228810750392937 : Nat.Prime 2228810750392937 := by
  apply lucas_primality 2228810750392937 (3 : ZMod 2228810750392937)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (661, 1), (421484635097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (661, 1), (421484635097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2228810750392937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_661
      · exact prime_twentyNineAA_421484635097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2228810750392937) ^ 1114405375196468 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2228810750392937) ^ 3371877080776 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2228810750392937) ^ 5288 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2306085341281439 : Nat.Prime 2306085341281439 := by
  apply lucas_primality 2306085341281439 (7 : ZMod 2306085341281439)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3001, 1), (384219483719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3001, 1), (384219483719, 1)] : List FactorBlock).map factorBlockValue).prod) = 2306085341281439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_3001
      · exact prime_twentyNineAA_384219483719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2306085341281439) ^ 1153042670640719 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2306085341281439) ^ 768438967438 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 2306085341281439) ^ 6002 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2845120878330713 : Nat.Prime 2845120878330713 := by
  apply lucas_primality 2845120878330713 (3 : ZMod 2845120878330713)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3301, 1), (107737082639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3301, 1), (107737082639, 1)] : List FactorBlock).map factorBlockValue).prod) = 2845120878330713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_3301
      · exact prime_twentyNineAA_107737082639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2845120878330713) ^ 1422560439165356 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2845120878330713) ^ 861896661112 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2845120878330713) ^ 26408 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2884478922809303 : Nat.Prime 2884478922809303 := by
  apply lucas_primality 2884478922809303 (5 : ZMod 2884478922809303)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (19, 1), (47, 1), (12491, 1), (1420847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (19, 1), (47, 1), (12491, 1), (1420847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2884478922809303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_47
      · exact prime_twentyNineAA_12491
      · exact prime_twentyNineAA_1420847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2884478922809303) ^ 1442239461404651 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 412068417544186 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 221882994062254 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 151814680147858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 61371891974666 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 230924579522 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2884478922809303) ^ 2030112266 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_4264046826756727 : Nat.Prime 4264046826756727 := by
  apply lucas_primality 4264046826756727 (5 : ZMod 4264046826756727)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15077, 1), (47136331573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15077, 1), (47136331573, 1)] : List FactorBlock).map factorBlockValue).prod) = 4264046826756727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_15077
      · exact prime_twentyNineAA_47136331573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4264046826756727) ^ 2132023413378363 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4264046826756727) ^ 1421348942252242 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4264046826756727) ^ 282817989438 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4264046826756727) ^ 90462 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_7350506732665067 : Nat.Prime 7350506732665067 := by
  apply lucas_primality 7350506732665067 (2 : ZMod 7350506732665067)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (83, 1), (281, 1), (1217, 1), (2729, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (83, 1), (281, 1), (1217, 1), (2729, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) = 7350506732665067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_83
      · exact prime_twentyNineAA_281
      · exact prime_twentyNineAA_1217
      · exact prime_twentyNineAA_2729
      · exact prime_twentyNineAA_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7350506732665067) ^ 3675253366332533 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 432382748980298 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 88560322080302 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 26158386948986 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 6039857627498 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 2693479931354 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7350506732665067) ^ 2633646267526 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_10212335170540199 : Nat.Prime 10212335170540199 := by
  apply lucas_primality 10212335170540199 (7 : ZMod 10212335170540199)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2329291, 1), (2192155289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2329291, 1), (2192155289, 1)] : List FactorBlock).map factorBlockValue).prod) = 10212335170540199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_2329291
      · exact prime_twentyNineAA_2192155289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10212335170540199) ^ 5106167585270099 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 10212335170540199) ^ 4384310578 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 10212335170540199) ^ 4658582 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_22253041320431843 : Nat.Prime 22253041320431843 := by
  apply lucas_primality 22253041320431843 (2 : ZMod 22253041320431843)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (108827, 1), (102240442723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (108827, 1), (102240442723, 1)] : List FactorBlock).map factorBlockValue).prod) = 22253041320431843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_108827
      · exact prime_twentyNineAA_102240442723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22253041320431843) ^ 11126520660215921 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22253041320431843) ^ 204480885446 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22253041320431843) ^ 217654 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_23480233181842277 : Nat.Prime 23480233181842277 := by
  apply lucas_primality 23480233181842277 (2 : ZMod 23480233181842277)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (863, 1), (26262245357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (863, 1), (26262245357, 1)] : List FactorBlock).map factorBlockValue).prod) = 23480233181842277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_twentyNineAA_863
      · exact prime_twentyNineAA_26262245357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23480233181842277) ^ 11740116590921138 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23480233181842277) ^ 3354319025977468 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23480233181842277) ^ 634600896806548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23480233181842277) ^ 27207686189852 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 23480233181842277) ^ 894068 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_26390306266333621 : Nat.Prime 26390306266333621 := by
  apply lucas_primality 26390306266333621 (2 : ZMod 26390306266333621)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (33833725982479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (33833725982479, 1)] : List FactorBlock).map factorBlockValue).prod) = 26390306266333621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyNineAA_33833725982479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26390306266333621) ^ 13195153133166810 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26390306266333621) ^ 8796768755444540 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26390306266333621) ^ 5278061253266724 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26390306266333621) ^ 2030023558948740 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 26390306266333621) ^ 780 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_31575357092789017 : Nat.Prime 31575357092789017 := by
  apply lucas_primality 31575357092789017 (10 : ZMod 31575357092789017)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 1), (12757, 1), (466655297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 1), (12757, 1), (466655297, 1)] : List FactorBlock).map factorBlockValue).prod) = 31575357092789017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_twentyNineAA_12757
      · exact prime_twentyNineAA_466655297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 31575357092789017) ^ 15787678546394508 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 31575357092789017) ^ 10525119030929672 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 31575357092789017) ^ 2428873622522232 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 31575357092789017) ^ 1857373946634648 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 31575357092789017) ^ 2475139695288 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (10 : ZMod 31575357092789017) ^ 67663128 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_31855792581598099 : Nat.Prime 31855792581598099 := by
  apply lucas_primality 31855792581598099 (2 : ZMod 31855792581598099)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (263, 1), (1021, 1), (191963407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (263, 1), (1021, 1), (191963407, 1)] : List FactorBlock).map factorBlockValue).prod) = 31855792581598099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_103
      · exact prime_t64_263
      · exact prime_twentyNineAA_1021
      · exact prime_twentyNineAA_191963407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31855792581598099) ^ 15927896290799049 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31855792581598099) ^ 10618597527199366 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31855792581598099) ^ 309279539627166 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31855792581598099) ^ 121124686622046 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31855792581598099) ^ 31200580393338 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31855792581598099) ^ 165947214 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_37572462522050549 : Nat.Prime 37572462522050549 := by
  apply lucas_primality 37572462522050549 (2 : ZMod 37572462522050549)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (11923, 1), (34252816553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (11923, 1), (34252816553, 1)] : List FactorBlock).map factorBlockValue).prod) = 37572462522050549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyNineAA_11923
      · exact prime_twentyNineAA_34252816553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37572462522050549) ^ 18786231261025274 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 37572462522050549) ^ 1633585327045676 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 37572462522050549) ^ 3151259122876 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 37572462522050549) ^ 1096916 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_40777299551039291 : Nat.Prime 40777299551039291 := by
  apply lucas_primality 40777299551039291 (2 : ZMod 40777299551039291)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19212269, 1), (212246141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19212269, 1), (212246141, 1)] : List FactorBlock).map factorBlockValue).prod) = 40777299551039291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_19212269
      · exact prime_twentyNineAA_212246141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40777299551039291) ^ 20388649775519645 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40777299551039291) ^ 8155459910207858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40777299551039291) ^ 2122461410 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40777299551039291) ^ 192122690 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_46252895592711281 : Nat.Prime 46252895592711281 := by
  apply lucas_primality 46252895592711281 (3 : ZMod 46252895592711281)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (1935893, 1), (27150317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (1935893, 1), (27150317, 1)] : List FactorBlock).map factorBlockValue).prod) = 46252895592711281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentyNineAA_1935893
      · exact prime_twentyNineAA_27150317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46252895592711281) ^ 23126447796355640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46252895592711281) ^ 9250579118542256 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46252895592711281) ^ 4204808690246480 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46252895592711281) ^ 23892278960 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 46252895592711281) ^ 1703585840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_53311787208700507 : Nat.Prime 53311787208700507 := by
  apply lucas_primality 53311787208700507 (2 : ZMod 53311787208700507)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (149, 1), (6625874622011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (149, 1), (6625874622011, 1)] : List FactorBlock).map factorBlockValue).prod) = 53311787208700507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_149
      · exact prime_twentyNineAA_6625874622011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53311787208700507) ^ 26655893604350253 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 53311787208700507) ^ 17770595736233502 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 53311787208700507) ^ 357797229588594 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 53311787208700507) ^ 8046 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_93872461782024187 : Nat.Prime 93872461782024187 := by
  apply lucas_primality 93872461782024187 (2 : ZMod 93872461782024187)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (151, 1), (141740066651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (151, 1), (141740066651, 1)] : List FactorBlock).map factorBlockValue).prod) = 93872461782024187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_43
      · exact prime_twentyNineAA_151
      · exact prime_twentyNineAA_141740066651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93872461782024187) ^ 46936230891012093 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93872461782024187) ^ 31290820594008062 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93872461782024187) ^ 5521909516589658 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93872461782024187) ^ 2183080506558702 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93872461782024187) ^ 621671932331286 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 93872461782024187) ^ 662286 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_108820654985960419 : Nat.Prime 108820654985960419 := by
  apply lucas_primality 108820654985960419 (2 : ZMod 108820654985960419)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (47713, 1), (5207154947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (47713, 1), (5207154947, 1)] : List FactorBlock).map factorBlockValue).prod) = 108820654985960419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_twentyNineAA_47713
      · exact prime_twentyNineAA_5207154947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108820654985960419) ^ 54410327492980209 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108820654985960419) ^ 36273551661986806 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108820654985960419) ^ 1490693903917266 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108820654985960419) ^ 2280733866786 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108820654985960419) ^ 20898294 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_156577804455856933 : Nat.Prime 156577804455856933 := by
  apply lucas_primality 156577804455856933 (2 : ZMod 156577804455856933)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (47, 1), (479, 1), (647, 1), (99533389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (47, 1), (479, 1), (647, 1), (99533389, 1)] : List FactorBlock).map factorBlockValue).prod) = 156577804455856933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_t64_479
      · exact prime_t64_647
      · exact prime_twentyNineAA_99533389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156577804455856933) ^ 78288902227928466 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 156577804455856933) ^ 52192601485285644 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 156577804455856933) ^ 3331442647996956 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 156577804455856933) ^ 326884769218908 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 156577804455856933) ^ 242005880148156 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 156577804455856933) ^ 1573118388 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_228727254399219431 : Nat.Prime 228727254399219431 := by
  apply lucas_primality 228727254399219431 (7 : ZMod 228727254399219431)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (107, 1), (5777399706977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (107, 1), (5777399706977, 1)] : List FactorBlock).map factorBlockValue).prod) = 228727254399219431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_t64_107
      · exact prime_twentyNineAA_5777399706977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 228727254399219431) ^ 114363627199609715 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 228727254399219431) ^ 45745450879843886 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 228727254399219431) ^ 6181817686465390 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 228727254399219431) ^ 2137637891581490 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 228727254399219431) ^ 39590 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_278564512273848001 : Nat.Prime 278564512273848001 := by
  apply lucas_primality 278564512273848001 (13 : ZMod 278564512273848001)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 3), (315281, 1), (12271439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 3), (315281, 1), (12271439, 1)] : List FactorBlock).map factorBlockValue).prod) = 278564512273848001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_315281
      · exact prime_twentyNineAA_12271439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 278564512273848001) ^ 139282256136924000 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 278564512273848001) ^ 92854837424616000 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 278564512273848001) ^ 55712902454769600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 278564512273848001) ^ 883543608000 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 278564512273848001) ^ 22700232000 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_305861497353472339 : Nat.Prime 305861497353472339 := by
  apply lucas_primality 305861497353472339 (2 : ZMod 305861497353472339)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (288005176415699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (288005176415699, 1)] : List FactorBlock).map factorBlockValue).prod) = 305861497353472339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_twentyNineAA_288005176415699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 305861497353472339) ^ 152930748676736169 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 305861497353472339) ^ 101953832451157446 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 305861497353472339) ^ 5184093175482582 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 305861497353472339) ^ 1062 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_398503943056251271 : Nat.Prime 398503943056251271 := by
  apply lucas_primality 398503943056251271 (3 : ZMod 398503943056251271)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (3673, 1), (24602152439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (3673, 1), (24602152439, 1)] : List FactorBlock).map factorBlockValue).prod) = 398503943056251271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_3673
      · exact prime_twentyNineAA_24602152439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 398503943056251271) ^ 199251971528125635 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 398503943056251271) ^ 132834647685417090 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 398503943056251271) ^ 79700788611250254 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 398503943056251271) ^ 56929134722321610 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 398503943056251271) ^ 108495492255990 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 398503943056251271) ^ 16197930 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_462562623243181039 : Nat.Prime 462562623243181039 := by
  apply lucas_primality 462562623243181039 (6 : ZMod 462562623243181039)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (37, 1), (71848807586701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (37, 1), (71848807586701, 1)] : List FactorBlock).map factorBlockValue).prod) = 462562623243181039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_37
      · exact prime_twentyNineAA_71848807586701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 462562623243181039) ^ 231281311621590519 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 462562623243181039) ^ 154187541081060346 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 462562623243181039) ^ 15950435284247622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 462562623243181039) ^ 12501692520085974 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 462562623243181039) ^ 6438 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_489762780201998969 : Nat.Prime 489762780201998969 := by
  apply lucas_primality 489762780201998969 (3 : ZMod 489762780201998969)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (27615383, 1), (45242713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (27615383, 1), (45242713, 1)] : List FactorBlock).map factorBlockValue).prod) = 489762780201998969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_27615383
      · exact prime_twentyNineAA_45242713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 489762780201998969) ^ 244881390100999484 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 489762780201998969) ^ 69966111457428424 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 489762780201998969) ^ 17735143496 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 489762780201998969) ^ 10825230136 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_569024175666142601 : Nat.Prime 569024175666142601 := by
  apply lucas_primality 569024175666142601 (3 : ZMod 569024175666142601)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (2845120878330713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (2845120878330713, 1)] : List FactorBlock).map factorBlockValue).prod) = 569024175666142601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_2845120878330713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 569024175666142601) ^ 284512087833071300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 569024175666142601) ^ 113804835133228520 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 569024175666142601) ^ 200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_614124136620628477 : Nat.Prime 614124136620628477 := by
  apply lucas_primality 614124136620628477 (2 : ZMod 614124136620628477)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (181, 1), (282745919254433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (181, 1), (282745919254433, 1)] : List FactorBlock).map factorBlockValue).prod) = 614124136620628477 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_181
      · exact prime_twentyNineAA_282745919254433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 614124136620628477) ^ 307062068310314238 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 614124136620628477) ^ 204708045540209492 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 614124136620628477) ^ 3392951031053196 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 614124136620628477) ^ 2172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_748940343939659537 : Nat.Prime 748940343939659537 := by
  apply lucas_primality 748940343939659537 (3 : ZMod 748940343939659537)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (157, 1), (461, 1), (92390778239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (157, 1), (461, 1), (92390778239, 1)] : List FactorBlock).map factorBlockValue).prod) = 748940343939659537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_157
      · exact prime_t64_461
      · exact prime_twentyNineAA_92390778239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 748940343939659537) ^ 374470171969829768 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 748940343939659537) ^ 106991477705665648 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 748940343939659537) ^ 4770320662036048 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 748940343939659537) ^ 1624599444554576 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 748940343939659537) ^ 8106224 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1668593810823586249 : Nat.Prime 1668593810823586249 := by
  apply lucas_primality 1668593810823586249 (13 : ZMod 1668593810823586249)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (107, 1), (325807, 1), (284903089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (107, 1), (325807, 1), (284903089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1668593810823586249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_107
      · exact prime_twentyNineAA_325807
      · exact prime_twentyNineAA_284903089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1668593810823586249) ^ 834296905411793124 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1668593810823586249) ^ 556197936941195416 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1668593810823586249) ^ 238370544403369464 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1668593810823586249) ^ 15594334680594264 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1668593810823586249) ^ 5121417927864 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 1668593810823586249) ^ 5856706632 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2778491544947395327 : Nat.Prime 2778491544947395327 := by
  apply lucas_primality 2778491544947395327 (3 : ZMod 2778491544947395327)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (7350506732665067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (7350506732665067, 1)] : List FactorBlock).map factorBlockValue).prod) = 2778491544947395327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyNineAA_7350506732665067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2778491544947395327) ^ 1389245772473697663 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778491544947395327) ^ 926163848315798442 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778491544947395327) ^ 396927363563913618 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2778491544947395327) ^ 378 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_9888115295662468993 : Nat.Prime 9888115295662468993 := by
  apply lucas_primality 9888115295662468993 (5 : ZMod 9888115295662468993)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 7), (83, 1), (425575557359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 7), (83, 1), (425575557359, 1)] : List FactorBlock).map factorBlockValue).prod) = 9888115295662468993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_twentyNineAA_425575557359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9888115295662468993) ^ 4944057647831234496 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9888115295662468993) ^ 3296038431887489664 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9888115295662468993) ^ 119133919224849024 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 9888115295662468993) ^ 23234688 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_14380164181141384921 : Nat.Prime 14380164181141384921 := by
  apply lucas_primality 14380164181141384921 (17 : ZMod 14380164181141384921)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (811, 1), (375593, 1), (56201281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (811, 1), (375593, 1), (56201281, 1)] : List FactorBlock).map factorBlockValue).prod) = 14380164181141384921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_811
      · exact prime_twentyNineAA_375593
      · exact prime_twentyNineAA_56201281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 14380164181141384921) ^ 7190082090570692460 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 4793388060380461640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 2876032836228276984 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 2054309168734483560 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 17731398497091720 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 38286560668440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (17 : ZMod 14380164181141384921) ^ 255868975320 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_17483129573013276911 : Nat.Prime 17483129573013276911 := by
  apply lucas_primality 17483129573013276911 (7 : ZMod 17483129573013276911)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (59, 1), (739, 1), (932511659537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (59, 1), (739, 1), (932511659537, 1)] : List FactorBlock).map factorBlockValue).prod) = 17483129573013276911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_t64_59
      · exact prime_twentyNineAA_739
      · exact prime_twentyNineAA_932511659537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 17483129573013276911) ^ 8741564786506638455 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 17483129573013276911) ^ 3496625914602655382 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 17483129573013276911) ^ 406584408674727370 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 17483129573013276911) ^ 296324230051072490 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 17483129573013276911) ^ 23657820802453690 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 17483129573013276911) ^ 18748430 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_19376349763226309279 : Nat.Prime 19376349763226309279 := by
  apply lucas_primality 19376349763226309279 (23 : ZMod 19376349763226309279)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (237976093, 1), (40710706523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (237976093, 1), (40710706523, 1)] : List FactorBlock).map factorBlockValue).prod) = 19376349763226309279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_237976093
      · exact prime_twentyNineAA_40710706523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 19376349763226309279) ^ 9688174881613154639 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (23 : ZMod 19376349763226309279) ^ 81421413046 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (23 : ZMod 19376349763226309279) ^ 475952186 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_19975009084271436037 : Nat.Prime 19975009084271436037 := by
  apply lucas_primality 19975009084271436037 (2 : ZMod 19975009084271436037)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (5413, 1), (951101, 1), (7519217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (5413, 1), (951101, 1), (7519217, 1)] : List FactorBlock).map factorBlockValue).prod) = 19975009084271436037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_5413
      · exact prime_twentyNineAA_951101
      · exact prime_twentyNineAA_7519217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19975009084271436037) ^ 9987504542135718018 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19975009084271436037) ^ 6658336361423812012 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19975009084271436037) ^ 464535094983056652 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19975009084271436037) ^ 3690191960885172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19975009084271436037) ^ 21001985156436 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19975009084271436037) ^ 2656527811908 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_22887641184164897281 : Nat.Prime 22887641184164897281 := by
  apply lucas_primality 22887641184164897281 (13 : ZMod 22887641184164897281)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 1), (7, 1), (127, 1), (461, 1), (7271719699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 1), (7, 1), (127, 1), (461, 1), (7271719699, 1)] : List FactorBlock).map factorBlockValue).prod) = 22887641184164897281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyNineAA_127
      · exact prime_t64_461
      · exact prime_twentyNineAA_7271719699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22887641184164897281) ^ 11443820592082448640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 7629213728054965760 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 4577528236832979456 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 3269663026309271040 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 180217647119408640 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 49647811679316480 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22887641184164897281) ^ 3147486720 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_24426137495113681549 : Nat.Prime 24426137495113681549 := by
  apply lucas_primality 24426137495113681549 (6 : ZMod 24426137495113681549)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (156577804455856933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (156577804455856933, 1)] : List FactorBlock).map factorBlockValue).prod) = 24426137495113681549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyNineAA_156577804455856933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24426137495113681549) ^ 12213068747556840774 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24426137495113681549) ^ 8142045831704560516 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24426137495113681549) ^ 1878933653470283196 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 24426137495113681549) ^ 156 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_40517047443752248843 : Nat.Prime 40517047443752248843 := by
  apply lucas_primality 40517047443752248843 (2 : ZMod 40517047443752248843)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 8), (11, 1), (83, 1), (3797, 1), (4799, 1), (185599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 8), (11, 1), (83, 1), (3797, 1), (4799, 1), (185599, 1)] : List FactorBlock).map factorBlockValue).prod) = 40517047443752248843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_83
      · exact prime_twentyNineAA_3797
      · exact prime_twentyNineAA_4799
      · exact prime_twentyNineAA_185599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40517047443752248843) ^ 20258523721876124421 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 13505682481250749614 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 3683367949432022622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 488157198117496974 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 10670805226165986 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 8442810469629558 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40517047443752248843) ^ 218304233555958 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_45595098791777951249 : Nat.Prime 45595098791777951249 := by
  apply lucas_primality 45595098791777951249 (3 : ZMod 45595098791777951249)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (1480643, 1), (39278214779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (1480643, 1), (39278214779, 1)] : List FactorBlock).map factorBlockValue).prod) = 45595098791777951249 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyNineAA_1480643
      · exact prime_twentyNineAA_39278214779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45595098791777951249) ^ 22797549395888975624 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 45595098791777951249) ^ 6513585541682564464 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 45595098791777951249) ^ 30794120386736 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 45595098791777951249) ^ 1160824112 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_47666536524117062509 : Nat.Prime 47666536524117062509 := by
  apply lucas_primality 47666536524117062509 (2 : ZMod 47666536524117062509)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (11203547, 1), (2930160707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (11203547, 1), (2930160707, 1)] : List FactorBlock).map factorBlockValue).prod) = 47666536524117062509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyNineAA_11203547
      · exact prime_twentyNineAA_2930160707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47666536524117062509) ^ 23833268262058531254 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47666536524117062509) ^ 15888845508039020836 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47666536524117062509) ^ 4333321502192460228 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47666536524117062509) ^ 4254593346564 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 47666536524117062509) ^ 16267550244 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_95556750010324967011 : Nat.Prime 95556750010324967011 := by
  apply lucas_primality 95556750010324967011 (3 : ZMod 95556750010324967011)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (487, 1), (509, 1), (619, 1), (20758822871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (487, 1), (509, 1), (619, 1), (20758822871, 1)] : List FactorBlock).map factorBlockValue).prod) = 95556750010324967011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_487
      · exact prime_twentyNineAA_509
      · exact prime_twentyNineAA_619
      · exact prime_twentyNineAA_20758822871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95556750010324967011) ^ 47778375005162483505 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 31852250003441655670 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 19111350002064993402 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 196215092423665230 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 187734282927946890 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 154372778691962790 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 95556750010324967011) ^ 4603187310 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_132048015801475018109 : Nat.Prime 132048015801475018109 := by
  apply lucas_primality 132048015801475018109 (2 : ZMod 132048015801475018109)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (45210467, 1), (730184980181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (45210467, 1), (730184980181, 1)] : List FactorBlock).map factorBlockValue).prod) = 132048015801475018109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_45210467
      · exact prime_twentyNineAA_730184980181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132048015801475018109) ^ 66024007900737509054 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 132048015801475018109) ^ 2920739920724 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 132048015801475018109) ^ 180841868 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_145368662340159434831 : Nat.Prime 145368662340159434831 := by
  apply lucas_primality 145368662340159434831 (7 : ZMod 145368662340159434831)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8287, 1), (4773451, 1), (367486159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8287, 1), (4773451, 1), (367486159, 1)] : List FactorBlock).map factorBlockValue).prod) = 145368662340159434831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_8287
      · exact prime_twentyNineAA_4773451
      · exact prime_twentyNineAA_367486159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 145368662340159434831) ^ 72684331170079717415 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 145368662340159434831) ^ 29073732468031886966 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 145368662340159434831) ^ 17541771731647090 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 145368662340159434831) ^ 30453577996330 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (7 : ZMod 145368662340159434831) ^ 395575884370 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_181160409868325382259 : Nat.Prime 181160409868325382259 := by
  apply lucas_primality 181160409868325382259 (2 : ZMod 181160409868325382259)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (393697, 1), (594511457011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (393697, 1), (594511457011, 1)] : List FactorBlock).map factorBlockValue).prod) = 181160409868325382259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyNineAA_393697
      · exact prime_twentyNineAA_594511457011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181160409868325382259) ^ 90580204934162691129 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 181160409868325382259) ^ 60386803289441794086 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 181160409868325382259) ^ 4213032787635474006 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 181160409868325382259) ^ 460151867726514 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 181160409868325382259) ^ 304721478 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_255409359211161583693 : Nat.Prime 255409359211161583693 := by
  apply lucas_primality 255409359211161583693 (5 : ZMod 255409359211161583693)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 1), (293, 1), (287122627684129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 1), (293, 1), (287122627684129, 1)] : List FactorBlock).map factorBlockValue).prod) = 255409359211161583693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentyNineAA_293
      · exact prime_twentyNineAA_287122627684129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 255409359211161583693) ^ 127704679605580791846 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 255409359211161583693) ^ 85136453070387194564 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 255409359211161583693) ^ 23219032655560143972 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 255409359211161583693) ^ 11104754748311373204 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 255409359211161583693) ^ 871704297649015644 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 255409359211161583693) ^ 889548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_410693684688946771699 : Nat.Prime 410693684688946771699 := by
  apply lucas_primality 410693684688946771699 (2 : ZMod 410693684688946771699)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (21323, 1), (13431377838839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (21323, 1), (13431377838839, 1)] : List FactorBlock).map factorBlockValue).prod) = 410693684688946771699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_239
      · exact prime_twentyNineAA_21323
      · exact prime_twentyNineAA_13431377838839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 410693684688946771699) ^ 205346842344473385849 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 410693684688946771699) ^ 136897894896315590566 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 410693684688946771699) ^ 1718383617945383982 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 410693684688946771699) ^ 19260595820895126 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 410693684688946771699) ^ 30577182 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_567714476014102226039 : Nat.Prime 567714476014102226039 := by
  apply lucas_primality 567714476014102226039 (23 : ZMod 567714476014102226039)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (278564512273848001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (278564512273848001, 1)] : List FactorBlock).map factorBlockValue).prod) = 567714476014102226039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_1019
      · exact prime_twentyNineAA_278564512273848001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 567714476014102226039) ^ 283857238007051113019 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (23 : ZMod 567714476014102226039) ^ 557129024547696002 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (23 : ZMod 567714476014102226039) ^ 2038 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1328201308244519733691 : Nat.Prime 1328201308244519733691 := by
  apply lucas_primality 1328201308244519733691 (2 : ZMod 1328201308244519733691)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (1768515109, 1), (2781578783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (1768515109, 1), (2781578783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1328201308244519733691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyNineAA_1768515109
      · exact prime_twentyNineAA_2781578783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1328201308244519733691) ^ 664100654122259866845 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1328201308244519733691) ^ 442733769414839911230 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1328201308244519733691) ^ 265640261648903946738 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1328201308244519733691) ^ 751026271410 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1328201308244519733691) ^ 477499079430 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_2971754392765132088563 : Nat.Prime 2971754392765132088563 := by
  apply lucas_primality 2971754392765132088563 (2 : ZMod 2971754392765132088563)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3914428097, 1), (18075707413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3914428097, 1), (18075707413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2971754392765132088563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyNineAA_3914428097
      · exact prime_twentyNineAA_18075707413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2971754392765132088563) ^ 1485877196382566044281 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971754392765132088563) ^ 990584797588377362854 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971754392765132088563) ^ 424536341823590298366 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971754392765132088563) ^ 759179711346 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2971754392765132088563) ^ 164405980074 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_10629371601443543786681 : Nat.Prime 10629371601443543786681 := by
  apply lucas_primality 10629371601443543786681 (3 : ZMod 10629371601443543786681)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (467, 1), (569024175666142601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (467, 1), (569024175666142601, 1)] : List FactorBlock).map factorBlockValue).prod) = 10629371601443543786681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_467
      · exact prime_twentyNineAA_569024175666142601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10629371601443543786681) ^ 5314685800721771893340 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10629371601443543786681) ^ 2125874320288708757336 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10629371601443543786681) ^ 22760967026645704040 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10629371601443543786681) ^ 18680 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20467179875666487235423 : Nat.Prime 20467179875666487235423 := by
  apply lucas_primality 20467179875666487235423 (3 : ZMod 20467179875666487235423)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (63587, 1), (185626757071159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (63587, 1), (185626757071159, 1)] : List FactorBlock).map factorBlockValue).prod) = 20467179875666487235423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyNineAA_63587
      · exact prime_twentyNineAA_185626757071159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20467179875666487235423) ^ 10233589937833243617711 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20467179875666487235423) ^ 6822393291888829078474 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20467179875666487235423) ^ 1203951757392146307966 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20467179875666487235423) ^ 321876796761389706 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20467179875666487235423) ^ 110259858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_25879975391706392791829 : Nat.Prime 25879975391706392791829 := by
  apply lucas_primality 25879975391706392791829 (2 : ZMod 25879975391706392791829)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (23, 1), (83, 1), (27438847, 1), (1037970761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (23, 1), (83, 1), (27438847, 1), (1037970761, 1)] : List FactorBlock).map factorBlockValue).prod) = 25879975391706392791829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_83
      · exact prime_twentyNineAA_27438847
      · exact prime_twentyNineAA_1037970761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25879975391706392791829) ^ 12939987695853196395914 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 3697139341672341827404 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 1522351493629787811284 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 1125216321378538817036 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 311806932430197503516 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 943187422988524 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 25879975391706392791829) ^ 24933241247348 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_33023069551606615218341 : Nat.Prime 33023069551606615218341 := by
  apply lucas_primality 33023069551606615218341 (2 : ZMod 33023069551606615218341)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (70321, 1), (23480233181842277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (70321, 1), (23480233181842277, 1)] : List FactorBlock).map factorBlockValue).prod) = 33023069551606615218341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyNineAA_70321
      · exact prime_twentyNineAA_23480233181842277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33023069551606615218341) ^ 16511534775803307609170 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33023069551606615218341) ^ 6604613910321323043668 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33023069551606615218341) ^ 469604663636845540 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33023069551606615218341) ^ 1406420 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_82752632384416353116533 : Nat.Prime 82752632384416353116533 := by
  apply lucas_primality 82752632384416353116533 (2 : ZMod 82752632384416353116533)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (255409359211161583693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (255409359211161583693, 1)] : List FactorBlock).map factorBlockValue).prod) = 82752632384416353116533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_255409359211161583693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82752632384416353116533) ^ 41376316192208176558266 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 82752632384416353116533) ^ 27584210794805451038844 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 82752632384416353116533) ^ 324 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_107132223149503317661451 : Nat.Prime 107132223149503317661451 := by
  apply lucas_primality 107132223149503317661451 (6 : ZMod 107132223149503317661451)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (149, 1), (14380164181141384921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (149, 1), (14380164181141384921, 1)] : List FactorBlock).map factorBlockValue).prod) = 107132223149503317661451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_149
      · exact prime_twentyNineAA_14380164181141384921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 107132223149503317661451) ^ 53566111574751658830725 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 107132223149503317661451) ^ 21426444629900663532290 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 107132223149503317661451) ^ 719008209057069246050 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 107132223149503317661451) ^ 7450 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_137107858944037709377717 : Nat.Prime 137107858944037709377717 := by
  apply lucas_primality 137107858944037709377717 (5 : ZMod 137107858944037709377717)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (37, 2), (103, 1), (127, 1), (2459761, 1), (23580397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (37, 2), (103, 1), (127, 1), (2459761, 1), (23580397, 1)] : List FactorBlock).map factorBlockValue).prod) = 137107858944037709377717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_37
      · exact prime_t64_103
      · exact prime_twentyNineAA_127
      · exact prime_twentyNineAA_2459761
      · exact prime_twentyNineAA_23580397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137107858944037709377717) ^ 68553929472018854688858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 45702619648012569792572 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 12464350813094337216156 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 3705617809298316469668 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 1331144261592599120172 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 1079589440504233932108 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 55740317430855156 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 137107858944037709377717) ^ 5814484757997828 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_178087385540259532717453 : Nat.Prime 178087385540259532717453 := by
  apply lucas_primality 178087385540259532717453 (2 : ZMod 178087385540259532717453)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149, 1), (1232632421, 1), (26934616883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149, 1), (1232632421, 1), (26934616883, 1)] : List FactorBlock).map factorBlockValue).prod) = 178087385540259532717453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_149
      · exact prime_twentyNineAA_1232632421
      · exact prime_twentyNineAA_26934616883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178087385540259532717453) ^ 89043692770129766358726 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 178087385540259532717453) ^ 59362461846753177572484 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 178087385540259532717453) ^ 1195217352619191494748 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 178087385540259532717453) ^ 144477284960412 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 178087385540259532717453) ^ 6611840306244 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_238115257097687625064793 : Nat.Prime 238115257097687625064793 := by
  apply lucas_primality 238115257097687625064793 (3 : ZMod 238115257097687625064793)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14487094841, 1), (2054546302339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14487094841, 1), (2054546302339, 1)] : List FactorBlock).map factorBlockValue).prod) = 238115257097687625064793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_14487094841
      · exact prime_twentyNineAA_2054546302339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 238115257097687625064793) ^ 119057628548843812532396 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 238115257097687625064793) ^ 16436370418712 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (3 : ZMod 238115257097687625064793) ^ 115896758728 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_431294290697299776814007 : Nat.Prime 431294290697299776814007 := by
  apply lucas_primality 431294290697299776814007 (5 : ZMod 431294290697299776814007)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (32341723, 1), (141867430349263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (32341723, 1), (141867430349263, 1)] : List FactorBlock).map factorBlockValue).prod) = 431294290697299776814007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_twentyNineAA_32341723
      · exact prime_twentyNineAA_141867430349263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 431294290697299776814007) ^ 215647145348649888407003 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 431294290697299776814007) ^ 9176474270155314400298 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 431294290697299776814007) ^ 13335538452830722 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 431294290697299776814007) ^ 3040121962 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_476230514195375250129587 : Nat.Prime 476230514195375250129587 := by
  apply lucas_primality 476230514195375250129587 (2 : ZMod 476230514195375250129587)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (238115257097687625064793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (238115257097687625064793, 1)] : List FactorBlock).map factorBlockValue).prod) = 476230514195375250129587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_238115257097687625064793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 476230514195375250129587) ^ 238115257097687625064793 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 476230514195375250129587) ^ 2 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_548431435776150837510869 : Nat.Prime 548431435776150837510869 := by
  apply lucas_primality 548431435776150837510869 (2 : ZMod 548431435776150837510869)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137107858944037709377717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137107858944037709377717, 1)] : List FactorBlock).map factorBlockValue).prod) = 548431435776150837510869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyNineAA_137107858944037709377717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 548431435776150837510869) ^ 274215717888075418755434 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 548431435776150837510869) ^ 4 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_640005593305740900073351 : Nat.Prime 640005593305740900073351 := by
  apply lucas_primality 640005593305740900073351 (6 : ZMod 640005593305740900073351)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (17, 1), (73, 1), (44879, 1), (433571, 1), (176692181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (17, 1), (73, 1), (44879, 1), (433571, 1), (176692181, 1)] : List FactorBlock).map factorBlockValue).prod) = 640005593305740900073351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_73
      · exact prime_twentyNineAA_44879
      · exact prime_twentyNineAA_433571
      · exact prime_twentyNineAA_176692181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 640005593305740900073351) ^ 320002796652870450036675 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 213335197768580300024450 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 128001118661148180014670 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 37647387841514170592550 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 8767199908297820548950 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 14260691933994538650 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 1476126386003078850 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 640005593305740900073351) ^ 3622150056010350 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_967430576720706708742367 : Nat.Prime 967430576720706708742367 := by
  apply lucas_primality 967430576720706708742367 (5 : ZMod 967430576720706708742367)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (22571, 1), (7738259, 1), (737147771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (22571, 1), (7738259, 1), (737147771, 1)] : List FactorBlock).map factorBlockValue).prod) = 967430576720706708742367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_twentyNineAA_22571
      · exact prime_twentyNineAA_7738259
      · exact prime_twentyNineAA_737147771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 967430576720706708742367) ^ 483715288360353354371183 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 967430576720706708742367) ^ 74417736670823592980182 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 967430576720706708742367) ^ 56907680983570982867198 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 967430576720706708742367) ^ 42861662164755957146 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 967430576720706708742367) ^ 125019151817056874 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 967430576720706708742367) ^ 1312397072581946 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3157356997788179920603139 : Nat.Prime 3157356997788179920603139 := by
  apply lucas_primality 3157356997788179920603139 (2 : ZMod 3157356997788179920603139)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (25879975391706392791829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (25879975391706392791829, 1)] : List FactorBlock).map factorBlockValue).prod) = 3157356997788179920603139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_twentyNineAA_25879975391706392791829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3157356997788179920603139) ^ 1578678498894089960301569 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3157356997788179920603139) ^ 51759950783412785583658 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3157356997788179920603139) ^ 122 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_8442683979064724392472171 : Nat.Prime 8442683979064724392472171 := by
  apply lucas_primality 8442683979064724392472171 (2 : ZMod 8442683979064724392472171)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (31, 1), (772853, 1), (4829423, 1), (561284881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (31, 1), (772853, 1), (4829423, 1), (561284881, 1)] : List FactorBlock).map factorBlockValue).prod) = 8442683979064724392472171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_twentyNineAA_772853
      · exact prime_twentyNineAA_4829423
      · exact prime_twentyNineAA_561284881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8442683979064724392472171) ^ 4221341989532362196236085 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 1688536795812944878494434 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 649437229158824953267090 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 272344644485958851370070 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 10924048918830261890 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 1748176537666036790 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8442683979064724392472171) ^ 15041709236890570 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_12098002695477009794576389 : Nat.Prime 12098002695477009794576389 := by
  apply lucas_primality 12098002695477009794576389 (2 : ZMod 12098002695477009794576389)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (353, 1), (369331, 1), (286403419834859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (353, 1), (369331, 1), (286403419834859, 1)] : List FactorBlock).map factorBlockValue).prod) = 12098002695477009794576389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyNineAA_353
      · exact prime_twentyNineAA_369331
      · exact prime_twentyNineAA_286403419834859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12098002695477009794576389) ^ 6049001347738504897288194 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12098002695477009794576389) ^ 4032667565159003264858796 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12098002695477009794576389) ^ 34271962310133172222596 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12098002695477009794576389) ^ 32756531933352493548 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12098002695477009794576389) ^ 42241125132 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_17903780490329945565446207 : Nat.Prime 17903780490329945565446207 := by
  apply lucas_primality 17903780490329945565446207 (5 : ZMod 17903780490329945565446207)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (307, 1), (410693684688946771699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (307, 1), (410693684688946771699, 1)] : List FactorBlock).map factorBlockValue).prod) = 17903780490329945565446207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_71
      · exact prime_t64_307
      · exact prime_twentyNineAA_410693684688946771699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17903780490329945565446207) ^ 8951890245164972782723103 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17903780490329945565446207) ^ 252165922399013317823186 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17903780490329945565446207) ^ 58318503225830441581258 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17903780490329945565446207) ^ 43594 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_20944251459365819033493883 : Nat.Prime 20944251459365819033493883 := by
  apply lucas_primality 20944251459365819033493883 (2 : ZMod 20944251459365819033493883)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (97, 1), (193, 1), (331, 1), (2158321061215577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (97, 1), (193, 1), (331, 1), (2158321061215577, 1)] : List FactorBlock).map factorBlockValue).prod) = 20944251459365819033493883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_97
      · exact prime_t64_193
      · exact prime_twentyNineAA_331
      · exact prime_twentyNineAA_2158321061215577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20944251459365819033493883) ^ 10472125729682909516746941 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 6981417153121939677831294 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 722215567564338587361858 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 215920118137791948798906 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 108519437613294399137274 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 63275684167268335448622 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (2 : ZMod 20944251459365819033493883) ^ 9703955466 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_64812362266506324683987687 : Nat.Prime 64812362266506324683987687 := by
  apply lucas_primality 64812362266506324683987687 (5 : ZMod 64812362266506324683987687)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (67, 1), (1987, 1), (245339, 1), (90197792637923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (67, 1), (1987, 1), (245339, 1), (90197792637923, 1)] : List FactorBlock).map factorBlockValue).prod) = 64812362266506324683987687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_67
      · exact prime_twentyNineAA_1987
      · exact prime_twentyNineAA_245339
      · exact prime_twentyNineAA_90197792637923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 64812362266506324683987687) ^ 32406181133253162341993843 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64812362266506324683987687) ^ 5892032933318756789453426 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64812362266506324683987687) ^ 967348690544870517671458 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64812362266506324683987687) ^ 32618199429545206182178 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64812362266506324683987687) ^ 264174722594069123474 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (5 : ZMod 64812362266506324683987687) ^ 718558186082 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_372671083032411366932929201 : Nat.Prime 372671083032411366932929201 := by
  apply lucas_primality 372671083032411366932929201 (79 : ZMod 372671083032411366932929201)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 372671083032411366932929201 - 1 by
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
    · change (79 : ZMod 372671083032411366932929201) ^ 186335541516205683466464600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 124223694344137122310976400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 74534216606482273386585840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 53238726147487338133275600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 33879189366582851539357200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 28667006387108566687148400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 21921828413671256878407600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 19614267528021650891206800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 12850727001117633342514800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 12021647839755205384933200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 10072191433308415322511600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 9089538610546618705681200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 8666769372846775975184400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 7929171979413007807083600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 7031529868536063527036400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 6316459034447650286998800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 372671083032411366932929201) ^ 6109362016924776507097200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_380952662655353841753660961 : Nat.Prime 380952662655353841753660961 := by
  apply lucas_primality 380952662655353841753660961 (89 : ZMod 380952662655353841753660961)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 380952662655353841753660961 - 1 by
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
    · change (89 : ZMod 380952662655353841753660961) ^ 190476331327676920876830480 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 126984220885117947251220320 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 76190532531070768350732192 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 54421808950764834536237280 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 34632060241395803795787360 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 29304050973488757057973920 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 22408980156197284809038880 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 20050140139755465355455840 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 16563159245884949641463520 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 13136298712253580750126240 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 12288795569527543282376160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 10296017909604157885234080 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 9291528357447654676918560 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 8859364247798926552410720 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 8105375801177741313907680 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 7187786087836864938748320 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 6456824790768709182265440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (89 : ZMod 380952662655353841753660961) ^ 6245125617300882651699360 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_552995800628739447706927201 : Nat.Prime 552995800628739447706927201 := by
  apply lucas_primality 552995800628739447706927201 (79 : ZMod 552995800628739447706927201)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 552995800628739447706927201 - 1 by
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
    · change (79 : ZMod 552995800628739447706927201) ^ 276497900314369723853463600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 184331933542913149235642400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 110599160125747889541385440 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 78999400089819921100989600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 50272345511703586155175200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 42538138509903034438994400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 32529164742867026335701600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 29105042138354707774048800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 24043295679510410769866400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 19068820711335843024376800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 14945832449425390478565600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 13487702454359498724559200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 12860367456482312737370400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 11765868098483818036317600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 10433883030730932975602400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 9372810180148126232320800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 552995800628739447706927201) ^ 9065504928339990946015200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_714286242478788453288114301 : Nat.Prime 714286242478788453288114301 := by
  apply lucas_primality 714286242478788453288114301 (6 : ZMod 714286242478788453288114301)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 714286242478788453288114301 - 1 by
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
    · change (6 : ZMod 714286242478788453288114301) ^ 357143121239394226644057150 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 238095414159596151096038100 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 142857248495757690657622860 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 102040891782684064755444900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 64935112952617132117101300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 54945095575291419483701100 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 42016837792869909016947900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 37594012762041497541479700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 31055923586034280577744100 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 24630560085475463906486700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 23041491692864143654455300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 19305033580507796034813900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 17421615670214352519222300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 16611307964622987285770100 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 15197579627208264963576900 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 13477098914694121760153100 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 12106546482691329716747700 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (6 : ZMod 714286242478788453288114301) ^ 11709610532439154971936300 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1038961807241874113873620801 : Nat.Prime 1038961807241874113873620801 := by
  apply lucas_primality 1038961807241874113873620801 (67 : ZMod 1038961807241874113873620801)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1038961807241874113873620801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
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
    · change (67 : ZMod 1038961807241874113873620801) ^ 519480903620937056936810400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 346320602413958037957873600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 207792361448374822774724160 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 148423115320267730553374400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 79920139018605701067201600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 61115400425992594933742400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 54682200381151269151243200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 45172252488777135385809600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 35826269215237038409435200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 33514897007802390770116800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 28080048844374976050638400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 25340531883948149118868800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 24161902493997072415665600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 22105570366848385401566400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 19603052966827813469313600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 17609522156641934133451200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (67 : ZMod 1038961807241874113873620801) ^ 17032160774456952686452800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1371429585559273830313179457 : Nat.Prime 1371429585559273830313179457 := by
  apply lucas_primality 1371429585559273830313179457 (30 : ZMod 1371429585559273830313179457)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371429585559273830313179457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
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
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 1371429585559273830313179457) ^ 685714792779636915156589728 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 457143195186424610104393152 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 195918512222753404330454208 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 124675416869024893664834496 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 105494583504559525408706112 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 80672328562310225312539968 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 72180504503119675279641024 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 59627373285185818709268672 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 47290675364112890700454464 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 44239664050299155816554176 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 37065664474574968386842688 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 33449502086811556836906816 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 31893711292076135588678592 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 29179352884239868730067648 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 25876029916212713779493952 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 23244569246767353056155584 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (30 : ZMod 1371429585559273830313179457) ^ 22482452222283177546117696 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_1804512612577991881991025601 : Nat.Prime 1804512612577991881991025601 := by
  apply lucas_primality 1804512612577991881991025601 (79 : ZMod 1804512612577991881991025601)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1804512612577991881991025601 - 1 by
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
    · change (79 : ZMod 1804512612577991881991025601) ^ 902256306288995940995512800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 601504204192663960663675200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 360902522515598376398205120 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 257787516082570268855860800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 164046601143453807453729600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 138808662505999375537771200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 106147800739881875411236800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 78457070112086603564827200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 62224572847516961447966400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 58210084276709415548097600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 48770611150756537351108800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 44012502745804680048561600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 41965409594837020511419200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 38393885373999827276404800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 34047407784490412867755200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 30584959535220201389678400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (79 : ZMod 1804512612577991881991025601) ^ 29582173976688391508049600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem prime_twentyNineAA_3809526626553538417536609601 : Nat.Prime 3809526626553538417536609601 := by
  apply lucas_primality 3809526626553538417536609601 (134 : ZMod 3809526626553538417536609601)
  · rw [← twentyNineAAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3809526626553538417536609601 - 1 by
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
    · change (134 : ZMod 3809526626553538417536609601) ^ 1904763313276769208768304800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 1269842208851179472512203200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 761905325310707683507321920 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 544218089507648345362372800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 346320602413958037957873600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 293040509734887570579739200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 224089801561972848090388800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 200501401397554653554558400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 165631592458849496414635200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 122887955695275432823761600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 102960179096041578852340800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 92915283574476546769185600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 88593642477989265524107200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 81053758011777413139076800 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 71877860878368649387483200 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 64568247907687091822654400 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide
    · change (134 : ZMod 3809526626553538417536609601) ^ 62451256173008826516993600 ≠ 1
      rw [← twentyNineAAFastPow_eq_pow]
      decide

private theorem phi_twentyNineAA_34285739638981845757829486400 : Nat.totient 34285739638981845757829486400 = 4511569685321458542182400000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 2), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486400 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486401 : Nat.totient 34285739638981845757829486401 = 34282582281984057577908872404 := by
  rw [← show ((([(10859, 1), (3157356997788179920603139, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486401 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyNineAA_10859, prime_twentyNineAA_3157356997788179920603139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486402 : Nat.totient 34285739638981845757829486402 = 17142869809602807581518589952 := by
  rw [← show ((([(2, 1), (1733684257, 1), (9888115295662468993, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486402 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyNineAA_1733684257, prime_twentyNineAA_9888115295662468993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486403 : Nat.totient 34285739638981845757829486403 = 22769952963409527366660180480 := by
  rw [← show ((([(3, 1), (337, 1), (1187, 1), (124909, 1), (228727254399219431, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486403 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyNineAA_337, prime_twentyNineAA_1187, prime_twentyNineAA_124909, prime_twentyNineAA_228727254399219431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486404 : Nat.totient 34285739638981845757829486404 = 17141772956619370577239690208 := by
  rw [← show ((([(2, 2), (15629, 1), (548431435776150837510869, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486404 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyNineAA_15629, prime_twentyNineAA_548431435776150837510869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486405 : Nat.totient 34285739638981845757829486405 = 27356976589224156824001802768 := by
  rw [← show ((([(5, 1), (383, 1), (17903780490329945565446207, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486405 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_383, prime_twentyNineAA_17903780490329945565446207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486406 : Nat.totient 34285739638981845757829486406 = 11421104428408138696222300800 := by
  rw [← show ((([(2, 1), (3, 1), (1709, 1), (17581, 1), (82471, 1), (2306085341281439, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486406 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_1709, prime_twentyNineAA_17581, prime_twentyNineAA_82471, prime_twentyNineAA_2306085341281439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486407 : Nat.totient 34285739638981845757829486407 = 28962523205124317520877992960 := by
  rw [← show ((([(7, 1), (71, 1), (2767, 1), (33289, 1), (748940343939659537, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486407 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_71, prime_twentyNineAA_2767, prime_twentyNineAA_33289, prime_twentyNineAA_748940343939659537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486408 : Nat.totient 34285739638981845757829486408 = 16941127883843591379142963200 := by
  rw [← show ((([(2, 3), (89, 1), (1861, 1), (980489, 1), (26390306266333621, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486408 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_89, prime_twentyNineAA_1861, prime_twentyNineAA_980489, prime_twentyNineAA_26390306266333621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486409 : Nat.totient 34285739638981845757829486409 = 22857159759321230505219657600 := by
  rw [← show ((([(3, 2), (3809526626553538417536609601, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486409 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyNineAA_3809526626553538417536609601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486410 : Nat.totient 34285739638981845757829486410 = 13714295855586394791047051536 := by
  rw [← show ((([(2, 1), (5, 1), (2164895844479, 1), (1583713125341279, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486410 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyNineAA_2164895844479, prime_twentyNineAA_1583713125341279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486411 : Nat.totient 34285739638981845757829486411 = 31168649545457466751334746920 := by
  rw [← show ((([(11, 1), (152287, 1), (20467179875666487235423, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486411 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_twentyNineAA_152287, prime_twentyNineAA_20467179875666487235423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486412 : Nat.totient 34285739638981845757829486412 = 11428579717592425477318765008 := by
  rw [← show ((([(2, 2), (3, 1), (70517107, 1), (40517047443752248843, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486412 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_70517107, prime_twentyNineAA_40517047443752248843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486413 : Nat.totient 34285739638981845757829486413 = 31645845304550855495091564480 := by
  rw [← show ((([(13, 1), (13003, 1), (330271, 1), (614124136620628477, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486413 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_twentyNineAA_13003, prime_twentyNineAA_330271, prime_twentyNineAA_614124136620628477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486414 : Nat.totient 34285739638981845757829486414 = 14693876682263562187753557408 := by
  rw [← show ((([(2, 1), (7, 1), (1663027, 1), (5068927, 1), (290516063034469, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486414 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyNineAA_1663027, prime_twentyNineAA_5068927, prime_twentyNineAA_290516063034469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486415 : Nat.totient 34285739638981845757829486415 = 18285704033421842283112864416 := by
  rw [← show ((([(3, 1), (5, 1), (769147, 1), (2971754392765132088563, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486415 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyNineAA_769147, prime_twentyNineAA_2971754392765132088563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486416 : Nat.totient 34285739638981845757829486416 = 17094305326710360484575544320 := by
  rw [← show ((([(2, 4), (353, 1), (15233027, 1), (398503943056251271, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486416 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyNineAA_353, prime_twentyNineAA_15233027, prime_twentyNineAA_398503943056251271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486417 : Nat.totient 34285739638981845757829486417 = 32268931145194016954957838400 := by
  rw [← show ((([(17, 1), (115357391, 1), (17483129573013276911, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486417 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_twentyNineAA_115357391, prime_twentyNineAA_17483129573013276911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486418 : Nat.totient 34285739638981845757829486418 = 11326770321149740872985920000 := by
  rw [← show ((([(2, 1), (3, 2), (113, 1), (26387, 1), (46831, 1), (22034891, 1), (619053551, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486418 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_113, prime_twentyNineAA_26387, prime_twentyNineAA_46831, prime_twentyNineAA_22034891, prime_twentyNineAA_619053551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486419 : Nat.totient 34285739638981845757829486419 = 32481227026403853875838460800 := by
  rw [← show ((([(19, 1), (1804512612577991881991025601, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486419 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_twentyNineAA_1804512612577991881991025601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486420 : Nat.totient 34285739638981845757829486420 = 13632174323364800735873372160 := by
  rw [← show ((([(2, 2), (5, 1), (167, 1), (86058616961, 1), (119281390651783, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486420 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_167, prime_twentyNineAA_86058616961, prime_twentyNineAA_119281390651783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486421 : Nat.totient 34285739638981845757829486421 = 19584171155155671542244510000 := by
  rw [← show ((([(3, 1), (7, 1), (2551, 1), (640005593305740900073351, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentyNineAA_2551, prime_twentyNineAA_640005593305740900073351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486422 : Nat.totient 34285739638981845757829486422 = 15550556789490639456677934720 := by
  rw [← show ((([(2, 1), (11, 1), (463, 1), (73823, 1), (45595098791777951249, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyNineAA_463, prime_twentyNineAA_73823, prime_twentyNineAA_45595098791777951249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486423 : Nat.totient 34285739638981845757829486423 = 32795055306852200290097769116 := by
  rw [← show ((([(23, 2), (64812362266506324683987687, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_twentyNineAA_64812362266506324683987687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486424 : Nat.totient 34285739638981845757829486424 = 11428355119212926563271625984 := by
  rw [← show ((([(2, 3), (3, 1), (50857, 1), (281840327, 1), (99666316795559, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_50857, prime_twentyNineAA_281840327, prime_twentyNineAA_99666316795559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486425 : Nat.totient 34285739638981845757829486425 = 27428591711185476606263589120 := by
  rw [← show ((([(5, 2), (1371429585559273830313179457, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_twentyNineAA_1371429585559273830313179457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486426 : Nat.totient 34285739638981845757829486426 = 15679011493338204693770998848 := by
  rw [← show ((([(2, 1), (13, 1), (109, 1), (12098002695477009794576389, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_109, prime_twentyNineAA_12098002695477009794576389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486427 : Nat.totient 34285739638981845757829486427 = 22857159732874040327641854624 := by
  rw [← show ((([(3, 4), (864256643, 1), (489762780201998969, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyNineAA_864256643, prime_twentyNineAA_489762780201998969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486428 : Nat.totient 34285739638981845757829486428 = 14692895385117892328546489664 := by
  rw [← show ((([(2, 2), (7, 1), (14797, 1), (82752632384416353116533, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyNineAA_14797, prime_twentyNineAA_82752632384416353116533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486429 : Nat.totient 34285739638981845757829486429 = 32775535179892277906027333376 := by
  rw [← show ((([(29, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486430 : Nat.totient 34285739638981845757829486430 = 9006403231777173637500543744 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (67, 1), (540218179, 1), (31575357092789017, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_67, prime_twentyNineAA_540218179, prime_twentyNineAA_31575357092789017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486431 : Nat.totient 34285739638981845757829486431 = 32926467518352425130641463000 := by
  rw [← show ((([(31, 1), (131, 1), (8442683979064724392472171, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_twentyNineAA_131, prime_twentyNineAA_8442683979064724392472171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486432 : Nat.totient 34285739638981845757829486432 = 16784619665278983784654694400 := by
  rw [← show ((([(2, 5), (73, 1), (137, 1), (107132223149503317661451, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_73, prime_t64_137, prime_twentyNineAA_107132223149503317661451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486433 : Nat.totient 34285739638981845757829486433 = 20779236144837482277472416000 := by
  rw [← show ((([(3, 1), (11, 1), (1038961807241874113873620801, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentyNineAA_1038961807241874113873620801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486434 : Nat.totient 34285739638981845757829486434 = 16134465711952351874717907264 := by
  rw [← show ((([(2, 1), (17, 1), (31655282299, 1), (31855792581598099, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyNineAA_31655282299, prime_twentyNineAA_31855792581598099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486435 : Nat.totient 34285739638981845757829486435 = 23354353036293422303569622400 := by
  rw [← show ((([(5, 1), (7, 1), (151, 1), (136099, 1), (47666536524117062509, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486435 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_twentyNineAA_151, prime_twentyNineAA_136099, prime_twentyNineAA_47666536524117062509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486436 : Nat.totient 34285739638981845757829486436 = 11428578295084425634823062848 := by
  rw [← show ((([(2, 2), (3, 2), (7212389, 1), (132048015801475018109, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486436 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_7212389, prime_twentyNineAA_132048015801475018109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486437 : Nat.totient 34285739638981845757829486437 = 33250767632992766380509288000 := by
  rw [← show ((([(37, 1), (311, 1), (31181, 1), (95556750010324967011, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486437 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_t64_311, prime_twentyNineAA_31181, prime_twentyNineAA_95556750010324967011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486438 : Nat.totient 34285739638981845757829486438 = 16212688722328838142643497504 := by
  rw [← show ((([(2, 1), (19, 1), (587, 1), (62927, 1), (24426137495113681549, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486438 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentyNineAA_587, prime_twentyNineAA_62927, prime_twentyNineAA_24426137495113681549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486439 : Nat.totient 34285739638981845757829486439 = 21098916700909612668906527328 := by
  rw [← show ((([(3, 1), (13, 1), (10318483017383, 1), (85198718428247, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486439 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_twentyNineAA_10318483017383, prime_twentyNineAA_85198718428247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486440 : Nat.totient 34285739638981845757829486440 = 13702503675468308748230921472 := by
  rw [← show ((([(2, 3), (5, 1), (1163, 1), (1654987469, 1), (445327081993063, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486440 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyNineAA_1163, prime_twentyNineAA_1654987469, prime_twentyNineAA_445327081993063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486441 : Nat.totient 34285739638981845757829486441 = 33262028206930229343351398400 := by
  rw [← show ((([(41, 1), (191, 1), (2713, 1), (549257, 1), (1644173, 1), (1786995227, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_191, prime_twentyNineAA_2713, prime_twentyNineAA_549257, prime_twentyNineAA_1644173, prime_twentyNineAA_1786995227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486442 : Nat.totient 34285739638981845757829486442 = 9795909672721971282278530800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (614611, 1), (1328201308244519733691, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentyNineAA_614611, prime_twentyNineAA_1328201308244519733691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486443 : Nat.totient 34285739638981845757829486443 = 33426432922087488637939606560 := by
  rw [← show ((([(43, 1), (541, 1), (530443, 1), (2778491544947395327, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_twentyNineAA_541, prime_twentyNineAA_530443, prime_twentyNineAA_2778491544947395327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486444 : Nat.totient 34285739638981845757829486444 = 15555936336089162577008477760 := by
  rw [← show ((([(2, 2), (11, 1), (547, 1), (334080829, 1), (4264046826756727, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyNineAA_547, prime_twentyNineAA_334080829, prime_twentyNineAA_4264046826756727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486445 : Nat.totient 34285739638981845757829486445 = 18266446843277398468203957120 := by
  rw [← show ((([(3, 2), (5, 1), (967, 1), (49211, 1), (923266907, 1), (17341436719, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyNineAA_967, prime_twentyNineAA_49211, prime_twentyNineAA_923266907, prime_twentyNineAA_17341436719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486446 : Nat.totient 34285739638981845757829486446 = 16397293807250868387084035200 := by
  rw [← show ((([(2, 1), (23, 1), (70121, 1), (10629371601443543786681, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentyNineAA_70121, prime_twentyNineAA_10629371601443543786681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486447 : Nat.totient 34285739638981845757829486447 = 33556255816773308689382242432 := by
  rw [← show ((([(47, 1), (327297336473, 1), (2228810750392937, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_twentyNineAA_327297336473, prime_twentyNineAA_2228810750392937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486448 : Nat.totient 34285739638981845757829486448 = 11428579879660615252609828800 := by
  rw [← show ((([(2, 4), (3, 1), (714286242478788453288114301, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_714286242478788453288114301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486449 : Nat.totient 34285739638981845757829486449 = 29324835063653698275646383360 := by
  rw [← show ((([(7, 2), (467, 1), (2286629, 1), (434334487, 1), (1508622361, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_467, prime_twentyNineAA_2286629, prime_twentyNineAA_434334487, prime_twentyNineAA_1508622361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486450 : Nat.totient 34285739638981845757829486450 = 13714000424071376305104645120 := by
  rw [← show ((([(2, 1), (5, 2), (53777, 1), (339373, 1), (37572462522050549, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyNineAA_53777, prime_twentyNineAA_339373, prime_twentyNineAA_37572462522050549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486451 : Nat.totient 34285739638981845757829486451 = 21512339138491513284475084800 := by
  rw [← show ((([(3, 1), (17, 1), (77201, 1), (6820277, 1), (1276786868332813, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_twentyNineAA_77201, prime_twentyNineAA_6820277, prime_twentyNineAA_1276786868332813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486452 : Nat.totient 34285739638981845757829486452 = 15717984760550127025421383680 := by
  rw [← show ((([(2, 2), (13, 1), (149, 1), (95672029, 1), (46252895592711281, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_149, prime_twentyNineAA_95672029, prime_twentyNineAA_46252895592711281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486453 : Nat.totient 34285739638981845757829486453 = 33638838885417853544950376208 := by
  rw [← show ((([(53, 1), (5944650379, 1), (108820654985960419, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_twentyNineAA_5944650379, prime_twentyNineAA_108820654985960419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486454 : Nat.totient 34285739638981845757829486454 = 11428579520110451735151836256 := by
  rw [← show ((([(2, 1), (3, 3), (31785773, 1), (19975009084271436037, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_31785773, prime_twentyNineAA_19975009084271436037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486455 : Nat.totient 34285739638981845757829486455 = 24523653543303168743756267520 := by
  rw [← show ((([(5, 1), (11, 1), (79, 1), (257, 1), (71967503, 1), (426632743730209, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_t64_79, prime_twentyNineAA_257, prime_twentyNineAA_71967503, prime_twentyNineAA_426632743730209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486456 : Nat.totient 34285739638981845757829486456 = 14689536196425515523106905600 := by
  rw [← show ((([(2, 3), (7, 1), (3413, 1), (314243, 1), (72751339, 1), (7846619701, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyNineAA_3413, prime_twentyNineAA_314243, prime_twentyNineAA_72751339, prime_twentyNineAA_7846619701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486457 : Nat.totient 34285739638981845757829486457 = 21654027954145092515075913600 := by
  rw [← show ((([(3, 1), (19, 1), (176047, 1), (54863833, 1), (62276456384551, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_twentyNineAA_176047, prime_twentyNineAA_54863833, prime_twentyNineAA_62276456384551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486458 : Nat.totient 34285739638981845757829486458 = 16551736363901542870701770800 := by
  rw [← show ((([(2, 1), (29, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486459 : Nat.totient 34285739638981845757829486459 = 33703598579395226939580689280 := by
  rw [← show ((([(59, 1), (36931, 1), (295153, 1), (53311787208700507, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_twentyNineAA_36931, prime_twentyNineAA_295153, prime_twentyNineAA_53311787208700507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486460 : Nat.totient 34285739638981845757829486460 = 9142853199652735518656739840 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (987023, 1), (6344777, 1), (91247008889671, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentyNineAA_987023, prime_twentyNineAA_6344777, prime_twentyNineAA_91247008889671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486461 : Nat.totient 34285739638981845757829486461 = 33575109336654673680965168640 := by
  rw [← show ((([(61, 1), (227, 1), (7562473, 1), (16020127, 1), (20437512653, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_t64_227, prime_twentyNineAA_7562473, prime_twentyNineAA_16020127, prime_twentyNineAA_20437512653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486462 : Nat.totient 34285739638981845757829486462 = 16589874018862183431207816000 := by
  rw [← show ((([(2, 1), (31, 1), (552995800628739447706927201, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_twentyNineAA_552995800628739447706927201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486463 : Nat.totient 34285739638981845757829486463 = 19160100805730678428024905984 := by
  rw [← show ((([(3, 2), (7, 1), (83, 1), (107, 1), (1303, 1), (206749, 1), (227469550795843, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_83, prime_t64_107, prime_twentyNineAA_1303, prime_twentyNineAA_206749, prime_twentyNineAA_227469550795843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486464 : Nat.totient 34285739638981845757829486464 = 17142833485764457976342080512 := by
  rw [← show ((([(2, 7), (471817, 1), (567714476014102226039, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486464 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyNineAA_471817, prime_twentyNineAA_567714476014102226039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486465 : Nat.totient 34285739638981845757829486465 = 25297997915140815708802335936 := by
  rw [← show ((([(5, 1), (13, 1), (1223, 1), (431294290697299776814007, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486465 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_twentyNineAA_1223, prime_twentyNineAA_431294290697299776814007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486466 : Nat.totient 34285739638981845757829486466 = 10386056324707935948081800640 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (2917, 1), (178087385540259532717453, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486466 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_twentyNineAA_2917, prime_twentyNineAA_178087385540259532717453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486467 : Nat.totient 34285739638981845757829486467 = 34180005321476905636264942080 := by
  rw [← show ((([(367, 1), (2777, 1), (21964618141, 1), (1531609041593, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486467 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyNineAA_367, prime_twentyNineAA_2777, prime_twentyNineAA_21964618141, prime_twentyNineAA_1531609041593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486468 : Nat.totient 34285739638981845757829486468 = 16134465092418852638433408128 := by
  rw [← show ((([(2, 2), (17, 1), (26021519, 1), (19376349763226309279, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486468 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyNineAA_26021519, prime_twentyNineAA_19376349763226309279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486469 : Nat.totient 34285739638981845757829486469 = 21835636665889917728281019904 := by
  rw [← show ((([(3, 1), (23, 1), (809, 1), (30829, 1), (408803939, 1), (48735048319, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486469 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_twentyNineAA_809, prime_twentyNineAA_30829, prime_twentyNineAA_408803939, prime_twentyNineAA_48735048319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486470 : Nat.totient 34285739638981845757829486470 = 11754999950613913393380908928 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (114269, 1), (1486003, 1), (2884478922809303, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486470 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_twentyNineAA_114269, prime_twentyNineAA_1486003, prime_twentyNineAA_2884478922809303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486471 : Nat.totient 34285739638981845757829486471 = 34264795387522479938795990952 := by
  rw [← show ((([(1637, 1), (20944251459365819033493883, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486471 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyNineAA_1637, prime_twentyNineAA_20944251459365819033493883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486472 : Nat.totient 34285739638981845757829486472 = 11347750089315967111464775680 := by
  rw [← show ((([(2, 3), (3, 2), (241, 1), (347, 1), (18617, 1), (305861497353472339, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486472 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyNineAA_241, prime_twentyNineAA_347, prime_twentyNineAA_18617, prime_twentyNineAA_305861497353472339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486473 : Nat.totient 34285739638981845757829486473 = 34285739638519283060465012628 := by
  rw [← show ((([(74121292807, 1), (462562623243181039, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486473 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyNineAA_74121292807, prime_twentyNineAA_462562623243181039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486474 : Nat.totient 34285739638981845757829486474 = 16679529847329632193396689280 := by
  rw [← show ((([(2, 1), (37, 1), (870407, 1), (5326346873, 1), (99937845391, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486474 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_twentyNineAA_870407, prime_twentyNineAA_5326346873, prime_twentyNineAA_99937845391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486475 : Nat.totient 34285739638981845757829486475 = 18285727803702085738101445920 := by
  rw [← show ((([(3, 1), (5, 2), (4869832819, 1), (93872461782024187, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486475 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyNineAA_4869832819, prime_twentyNineAA_93872461782024187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486476 : Nat.totient 34285739638981845757829486476 = 16218025733628628013109394080 := by
  rw [← show ((([(2, 2), (19, 2), (719, 1), (33023069551606615218341, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486476 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_719, prime_twentyNineAA_33023069551606615218341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486477 : Nat.totient 34285739638981845757829486477 = 26716160657532562834181034240 := by
  rw [← show ((([(7, 1), (11, 1), (266853049, 1), (1668593810823586249, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486477 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_twentyNineAA_266853049, prime_twentyNineAA_1668593810823586249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486478 : Nat.totient 34285739638981845757829486478 = 10400874430026995462830158240 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (71, 1), (476230514195375250129587, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486478 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_t64_71, prime_twentyNineAA_476230514195375250129587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486479 : Nat.totient 34285739638981845757829486479 = 34273481594179058155117657536 := by
  rw [← show ((([(2797, 1), (8211413993, 1), (1492805092926899, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486479 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyNineAA_2797, prime_twentyNineAA_8211413993, prime_twentyNineAA_1492805092926899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486480 : Nat.totient 34285739638981845757829486480 = 13683338077137675688452024704 := by
  rw [← show ((([(2, 4), (5, 1), (443, 1), (967430576720706708742367, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486480 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyNineAA_443, prime_twentyNineAA_967430576720706708742367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486481 : Nat.totient 34285739638981845757829486481 = 22846831144266575757617712000 := by
  rw [← show ((([(3, 3), (2213, 1), (773603081, 1), (741737359699151, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyNineAA_2213, prime_twentyNineAA_773603081, prime_twentyNineAA_741737359699151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486482 : Nat.totient 34285739638981845757829486482 = 16724750127900131051126784000 := by
  rw [← show ((([(2, 1), (41, 1), (18268321, 1), (22887641184164897281, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_twentyNineAA_18268321, prime_twentyNineAA_22887641184164897281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486483 : Nat.totient 34285739638981845757829486483 = 33786646300275503539485935616 := by
  rw [← show ((([(97, 1), (233, 1), (3691173029, 1), (410980734244127, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_97, prime_t64_233, prime_twentyNineAA_3691173029, prime_twentyNineAA_410980734244127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486484 : Nat.totient 34285739638981845757829486484 = 9795817509547823797230080640 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (90731, 1), (72614743, 1), (61951772236997, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentyNineAA_90731, prime_twentyNineAA_72614743, prime_twentyNineAA_61951772236997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486485 : Nat.totient 34285739638981845757829486485 = 25813816030455517251097896960 := by
  rw [← show ((([(5, 1), (17, 1), (19423, 1), (3381285577, 1), (6141810816871, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_twentyNineAA_19423, prime_twentyNineAA_3381285577, prime_twentyNineAA_6141810816871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486486 : Nat.totient 34285739638981845757829486486 = 16737703502999819653401447744 := by
  rw [← show ((([(2, 1), (43, 1), (2579, 1), (6946633, 1), (22253041320431843, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_twentyNineAA_2579, prime_twentyNineAA_6946633, prime_twentyNineAA_22253041320431843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486487 : Nat.totient 34285739638981845757829486487 = 22068981836586015660212083200 := by
  rw [← show ((([(3, 1), (29, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486488 : Nat.totient 34285739638981845757829486488 = 15430124457354879309752128000 := by
  rw [← show ((([(2, 3), (11, 1), (101, 1), (12931823, 1), (78926879, 1), (3779416853, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_101, prime_twentyNineAA_12931823, prime_twentyNineAA_78926879, prime_twentyNineAA_3779416853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486489 : Nat.totient 34285739638981845757829486489 = 33999241409864028277212710400 := by
  rw [← show ((([(197, 1), (331, 1), (3617, 1), (145368662340159434831, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_197, prime_twentyNineAA_331, prime_twentyNineAA_3617, prime_twentyNineAA_145368662340159434831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486490 : Nat.totient 34285739638981845757829486490 = 9142863903728492202087863040 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (380952662655353841753660961, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentyNineAA_380952662655353841753660961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486491 : Nat.totient 34285739638981845757829486491 = 27127165571908653156947165088 := by
  rw [← show ((([(7, 1), (13, 1), (2079739, 1), (181160409868325382259, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_twentyNineAA_2079739, prime_twentyNineAA_181160409868325382259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486492 : Nat.totient 34285739638981845757829486492 = 16397527653426100145048884800 := by
  rw [← show ((([(2, 2), (23, 1), (372671083032411366932929201, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_twentyNineAA_372671083032411366932929201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486493 : Nat.totient 34285739638981845757829486493 = 22067908739425884095399116800 := by
  rw [← show ((([(3, 1), (31, 1), (449, 1), (14813, 1), (18911, 1), (13980277, 1), (209657759, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_twentyNineAA_449, prime_twentyNineAA_14813, prime_twentyNineAA_18911, prime_twentyNineAA_13980277, prime_twentyNineAA_209657759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486494 : Nat.totient 34285739638981845757829486494 = 16656665615338698405705235968 := by
  rw [← show ((([(2, 1), (47, 1), (139, 1), (22193, 1), (2888807, 1), (40929489517909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_t64_139, prime_twentyNineAA_22193, prime_twentyNineAA_2888807, prime_twentyNineAA_40929489517909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486495 : Nat.totient 34285739638981845757829486495 = 25970727653683952468763780864 := by
  rw [← show ((([(5, 1), (19, 1), (1823, 1), (46913371289, 1), (4219943201143, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_twentyNineAA_1823, prime_twentyNineAA_46913371289, prime_twentyNineAA_4219943201143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486496 : Nat.totient 34285739638981845757829486496 = 11410703695603322901877579776 := by
  rw [← show ((([(2, 5), (3, 1), (997, 1), (1789, 1), (363719, 1), (550517086187513, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_997, prime_t64_1789, prime_twentyNineAA_363719, prime_twentyNineAA_550517086187513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486497 : Nat.totient 34285739638981845757829486497 = 33394528839430098040948283520 := by
  rw [← show ((([(67, 1), (89, 1), (563019781, 1), (10212335170540199, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_67, prime_t64_89, prime_twentyNineAA_563019781, prime_twentyNineAA_10212335170540199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486498 : Nat.totient 34285739638981845757829486498 = 14567477126808134604249538560 := by
  rw [← show ((([(2, 1), (7, 2), (127, 1), (1361, 1), (20273080687, 1), (99840294209, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyNineAA_127, prime_twentyNineAA_1361, prime_twentyNineAA_20273080687, prime_twentyNineAA_99840294209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyNineAA_34285739638981845757829486499 : Nat.totient 34285739638981845757829486499 = 20754987567265858178011996800 := by
  rw [← show ((([(3, 2), (11, 1), (857, 1), (9910123, 1), (40777299551039291, 1)] : List FactorBlock).map factorBlockValue).prod) = 34285739638981845757829486499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentyNineAA_857, prime_twentyNineAA_9910123, prime_twentyNineAA_40777299551039291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyNineAA : certifiedKill 1 34285739638981845757829486399 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyNineAA_34285739638981845757829486400, phi_twentyNineAA_34285739638981845757829486401, phi_twentyNineAA_34285739638981845757829486402,
    phi_twentyNineAA_34285739638981845757829486403, phi_twentyNineAA_34285739638981845757829486404, phi_twentyNineAA_34285739638981845757829486405,
    phi_twentyNineAA_34285739638981845757829486406, phi_twentyNineAA_34285739638981845757829486407, phi_twentyNineAA_34285739638981845757829486408,
    phi_twentyNineAA_34285739638981845757829486409, phi_twentyNineAA_34285739638981845757829486410, phi_twentyNineAA_34285739638981845757829486411,
    phi_twentyNineAA_34285739638981845757829486412, phi_twentyNineAA_34285739638981845757829486413, phi_twentyNineAA_34285739638981845757829486414,
    phi_twentyNineAA_34285739638981845757829486415, phi_twentyNineAA_34285739638981845757829486416, phi_twentyNineAA_34285739638981845757829486417,
    phi_twentyNineAA_34285739638981845757829486418, phi_twentyNineAA_34285739638981845757829486419, phi_twentyNineAA_34285739638981845757829486420,
    phi_twentyNineAA_34285739638981845757829486421, phi_twentyNineAA_34285739638981845757829486422, phi_twentyNineAA_34285739638981845757829486423,
    phi_twentyNineAA_34285739638981845757829486424, phi_twentyNineAA_34285739638981845757829486425, phi_twentyNineAA_34285739638981845757829486426,
    phi_twentyNineAA_34285739638981845757829486427, phi_twentyNineAA_34285739638981845757829486428, phi_twentyNineAA_34285739638981845757829486429,
    phi_twentyNineAA_34285739638981845757829486430, phi_twentyNineAA_34285739638981845757829486431, phi_twentyNineAA_34285739638981845757829486432,
    phi_twentyNineAA_34285739638981845757829486433, phi_twentyNineAA_34285739638981845757829486434, phi_twentyNineAA_34285739638981845757829486435,
    phi_twentyNineAA_34285739638981845757829486436, phi_twentyNineAA_34285739638981845757829486437, phi_twentyNineAA_34285739638981845757829486438,
    phi_twentyNineAA_34285739638981845757829486439, phi_twentyNineAA_34285739638981845757829486440, phi_twentyNineAA_34285739638981845757829486441,
    phi_twentyNineAA_34285739638981845757829486442, phi_twentyNineAA_34285739638981845757829486443, phi_twentyNineAA_34285739638981845757829486444,
    phi_twentyNineAA_34285739638981845757829486445, phi_twentyNineAA_34285739638981845757829486446, phi_twentyNineAA_34285739638981845757829486447,
    phi_twentyNineAA_34285739638981845757829486448, phi_twentyNineAA_34285739638981845757829486449, phi_twentyNineAA_34285739638981845757829486450,
    phi_twentyNineAA_34285739638981845757829486451, phi_twentyNineAA_34285739638981845757829486452, phi_twentyNineAA_34285739638981845757829486453,
    phi_twentyNineAA_34285739638981845757829486454, phi_twentyNineAA_34285739638981845757829486455, phi_twentyNineAA_34285739638981845757829486456,
    phi_twentyNineAA_34285739638981845757829486457, phi_twentyNineAA_34285739638981845757829486458, phi_twentyNineAA_34285739638981845757829486459,
    phi_twentyNineAA_34285739638981845757829486460, phi_twentyNineAA_34285739638981845757829486461, phi_twentyNineAA_34285739638981845757829486462,
    phi_twentyNineAA_34285739638981845757829486463, phi_twentyNineAA_34285739638981845757829486464, phi_twentyNineAA_34285739638981845757829486465,
    phi_twentyNineAA_34285739638981845757829486466, phi_twentyNineAA_34285739638981845757829486467, phi_twentyNineAA_34285739638981845757829486468,
    phi_twentyNineAA_34285739638981845757829486469, phi_twentyNineAA_34285739638981845757829486470, phi_twentyNineAA_34285739638981845757829486471,
    phi_twentyNineAA_34285739638981845757829486472, phi_twentyNineAA_34285739638981845757829486473, phi_twentyNineAA_34285739638981845757829486474,
    phi_twentyNineAA_34285739638981845757829486475, phi_twentyNineAA_34285739638981845757829486476, phi_twentyNineAA_34285739638981845757829486477,
    phi_twentyNineAA_34285739638981845757829486478, phi_twentyNineAA_34285739638981845757829486479, phi_twentyNineAA_34285739638981845757829486480,
    phi_twentyNineAA_34285739638981845757829486481, phi_twentyNineAA_34285739638981845757829486482, phi_twentyNineAA_34285739638981845757829486483,
    phi_twentyNineAA_34285739638981845757829486484, phi_twentyNineAA_34285739638981845757829486485, phi_twentyNineAA_34285739638981845757829486486,
    phi_twentyNineAA_34285739638981845757829486487, phi_twentyNineAA_34285739638981845757829486488, phi_twentyNineAA_34285739638981845757829486489,
    phi_twentyNineAA_34285739638981845757829486490, phi_twentyNineAA_34285739638981845757829486491, phi_twentyNineAA_34285739638981845757829486492,
    phi_twentyNineAA_34285739638981845757829486493, phi_twentyNineAA_34285739638981845757829486494, phi_twentyNineAA_34285739638981845757829486495,
    phi_twentyNineAA_34285739638981845757829486496, phi_twentyNineAA_34285739638981845757829486497, phi_twentyNineAA_34285739638981845757829486498,
    phi_twentyNineAA_34285739638981845757829486499]

end TotientTailPeriodKiller
end Erdos249257
