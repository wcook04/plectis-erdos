import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
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
  prime_t64_223
  prime_t64_229
  prime_t64_239
  prime_t64_269
  prime_t64_311
  prime_t64_349
  prime_t64_409
  prime_t64_421
  prime_t64_433
  prime_t64_461
  prime_t64_467
  prime_t64_491
  prime_t64_499
  prime_t64_641
  prime_t64_647
  prime_t64_751
  prime_t64_761
  prime_t64_787
  prime_t64_991
  prime_t64_1061
  prime_t64_1213
  prime_t64_1229
  prime_t64_1483
  prime_t64_1579
  prime_t64_1619
  prime_t64_1669
  prime_t64_2281
  prime_t64_2417
  prime_t64_2897
  prime_t64_2963
  prime_t64_3121
  prime_t64_3511
  prime_t64_4327
  prime_t64_4787
  prime_t64_5009
  prime_t64_6151
  prime_t64_9343
  prime_t64_10337
  prime_t64_13709
  prime_t64_39551
  prime_t64_45127
  prime_t64_97523
  prime_t64_210193
  prime_t64_241513
  prime_t64_623279
  prime_t64_911749
  prime_t64_1115447
  prime_t64_1214459
  prime_t64_1319293
  prime_t64_1789993
  prime_t64_2072201
  prime_t64_2567179
  prime_t64_3623449
  prime_t64_5250043
  prime_t64_9492089
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private theorem prime_free64SextD_131 : Nat.Prime 131 := by norm_num
private theorem prime_free64SextD_151 : Nat.Prime 151 := by norm_num
private theorem prime_free64SextD_173 : Nat.Prime 173 := by norm_num
private theorem prime_free64SextD_181 : Nat.Prime 181 := by norm_num
private theorem prime_free64SextD_199 : Nat.Prime 199 := by norm_num
private theorem prime_free64SextD_271 : Nat.Prime 271 := by norm_num
private theorem prime_free64SextD_277 : Nat.Prime 277 := by norm_num
private theorem prime_free64SextD_281 : Nat.Prime 281 := by norm_num
private theorem prime_free64SextD_331 : Nat.Prime 331 := by norm_num
private theorem prime_free64SextD_353 : Nat.Prime 353 := by norm_num
private theorem prime_free64SextD_367 : Nat.Prime 367 := by norm_num
private theorem prime_free64SextD_373 : Nat.Prime 373 := by norm_num
private theorem prime_free64SextD_379 : Nat.Prime 379 := by norm_num
private theorem prime_free64SextD_419 : Nat.Prime 419 := by norm_num
private theorem prime_free64SextD_457 : Nat.Prime 457 := by norm_num
private theorem prime_free64SextD_463 : Nat.Prime 463 := by norm_num
private theorem prime_free64SextD_541 : Nat.Prime 541 := by norm_num
private theorem prime_free64SextD_577 : Nat.Prime 577 := by norm_num
private theorem prime_free64SextD_631 : Nat.Prime 631 := by norm_num
private theorem prime_free64SextD_727 : Nat.Prime 727 := by norm_num
private theorem prime_free64SextD_733 : Nat.Prime 733 := by norm_num
private theorem prime_free64SextD_739 : Nat.Prime 739 := by norm_num
private theorem prime_free64SextD_743 : Nat.Prime 743 := by norm_num
private theorem prime_free64SextD_769 : Nat.Prime 769 := by norm_num
private theorem prime_free64SextD_809 : Nat.Prime 809 := by norm_num
private theorem prime_free64SextD_811 : Nat.Prime 811 := by norm_num
private theorem prime_free64SextD_821 : Nat.Prime 821 := by norm_num
private theorem prime_free64SextD_823 : Nat.Prime 823 := by norm_num
private theorem prime_free64SextD_907 : Nat.Prime 907 := by norm_num
private theorem prime_free64SextD_929 : Nat.Prime 929 := by norm_num
private theorem prime_free64SextD_953 : Nat.Prime 953 := by norm_num
private theorem prime_free64SextD_967 : Nat.Prime 967 := by norm_num
private theorem prime_free64SextD_983 : Nat.Prime 983 := by norm_num
private theorem prime_free64SextD_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_free64SextD_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_free64SextD_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_free64SextD_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_free64SextD_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_free64SextD_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_free64SextD_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_free64SextD_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_free64SextD_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_free64SextD_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_free64SextD_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_free64SextD_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_free64SextD_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_free64SextD_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_free64SextD_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_free64SextD_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_free64SextD_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_free64SextD_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_free64SextD_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_free64SextD_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_free64SextD_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_free64SextD_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_free64SextD_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_free64SextD_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_free64SextD_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_free64SextD_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_free64SextD_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_free64SextD_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_free64SextD_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_free64SextD_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_free64SextD_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_free64SextD_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_free64SextD_4013 : Nat.Prime 4013 := by norm_num
private theorem prime_free64SextD_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_free64SextD_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_free64SextD_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_free64SextD_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_free64SextD_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_free64SextD_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_free64SextD_4733 : Nat.Prime 4733 := by norm_num
private theorem prime_free64SextD_4919 : Nat.Prime 4919 := by norm_num
private theorem prime_free64SextD_4957 : Nat.Prime 4957 := by norm_num
private theorem prime_free64SextD_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_free64SextD_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_free64SextD_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_free64SextD_5507 : Nat.Prime 5507 := by norm_num
private theorem prime_free64SextD_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_free64SextD_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_free64SextD_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_free64SextD_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_free64SextD_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_free64SextD_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_free64SextD_6803 : Nat.Prime 6803 := by norm_num
private theorem prime_free64SextD_6911 : Nat.Prime 6911 := by norm_num
private theorem prime_free64SextD_7019 : Nat.Prime 7019 := by norm_num
private theorem prime_free64SextD_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_free64SextD_7829 : Nat.Prime 7829 := by norm_num
private theorem prime_free64SextD_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_free64SextD_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_free64SextD_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_free64SextD_8377 : Nat.Prime 8377 := by norm_num
private theorem prime_free64SextD_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_free64SextD_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_free64SextD_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_free64SextD_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_free64SextD_9521 : Nat.Prime 9521 := by norm_num
private theorem prime_free64SextD_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_free64SextD_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_free64SextD_11083 : Nat.Prime 11083 := by norm_num
private theorem prime_free64SextD_12421 : Nat.Prime 12421 := by norm_num
private theorem prime_free64SextD_12641 : Nat.Prime 12641 := by norm_num
private theorem prime_free64SextD_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_free64SextD_14627 : Nat.Prime 14627 := by norm_num
private theorem prime_free64SextD_14731 : Nat.Prime 14731 := by norm_num
private theorem prime_free64SextD_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_free64SextD_14939 : Nat.Prime 14939 := by norm_num
private theorem prime_free64SextD_15013 : Nat.Prime 15013 := by norm_num
private theorem prime_free64SextD_15887 : Nat.Prime 15887 := by norm_num
private theorem prime_free64SextD_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_free64SextD_17761 : Nat.Prime 17761 := by norm_num
private theorem prime_free64SextD_18133 : Nat.Prime 18133 := by norm_num
private theorem prime_free64SextD_21011 : Nat.Prime 21011 := by norm_num
private theorem prime_free64SextD_21683 : Nat.Prime 21683 := by norm_num
private theorem prime_free64SextD_22147 : Nat.Prime 22147 := by norm_num
private theorem prime_free64SextD_22343 : Nat.Prime 22343 := by norm_num
private theorem prime_free64SextD_22699 : Nat.Prime 22699 := by norm_num
private theorem prime_free64SextD_22943 : Nat.Prime 22943 := by norm_num
private theorem prime_free64SextD_23879 : Nat.Prime 23879 := by norm_num
private theorem prime_free64SextD_32429 : Nat.Prime 32429 := by norm_num
private theorem prime_free64SextD_34157 : Nat.Prime 34157 := by norm_num
private theorem prime_free64SextD_36313 : Nat.Prime 36313 := by norm_num
private theorem prime_free64SextD_38287 : Nat.Prime 38287 := by norm_num
private theorem prime_free64SextD_40591 : Nat.Prime 40591 := by norm_num
private theorem prime_free64SextD_41269 : Nat.Prime 41269 := by norm_num
private theorem prime_free64SextD_46649 : Nat.Prime 46649 := by norm_num
private theorem prime_free64SextD_53503 : Nat.Prime 53503 := by norm_num
private theorem prime_free64SextD_54049 : Nat.Prime 54049 := by norm_num
private theorem prime_free64SextD_54319 : Nat.Prime 54319 := by norm_num
private theorem prime_free64SextD_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_free64SextD_58369 : Nat.Prime 58369 := by norm_num
private theorem prime_free64SextD_62981 : Nat.Prime 62981 := by norm_num
private theorem prime_free64SextD_74071 : Nat.Prime 74071 := by norm_num
private theorem prime_free64SextD_75037 : Nat.Prime 75037 := by norm_num
private theorem prime_free64SextD_79493 : Nat.Prime 79493 := by norm_num
private theorem prime_free64SextD_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_free64SextD_82529 : Nat.Prime 82529 := by norm_num
private theorem prime_free64SextD_83243 : Nat.Prime 83243 := by norm_num
private theorem prime_free64SextD_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_free64SextD_94771 : Nat.Prime 94771 := by norm_num
private theorem prime_free64SextD_97157 : Nat.Prime 97157 := by norm_num
private theorem prime_free64SextD_97303 : Nat.Prime 97303 := by norm_num
private theorem prime_free64SextD_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_free64SextD_103087 : Nat.Prime 103087 := by norm_num
private theorem prime_free64SextD_105769 : Nat.Prime 105769 := by norm_num
private theorem prime_free64SextD_110681 : Nat.Prime 110681 := by norm_num
private theorem prime_free64SextD_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_free64SextD_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_free64SextD_116663 : Nat.Prime 116663 := by norm_num
private theorem prime_free64SextD_132751 : Nat.Prime 132751 := by norm_num
private theorem prime_free64SextD_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_free64SextD_144589 : Nat.Prime 144589 := by norm_num
private theorem prime_free64SextD_150869 : Nat.Prime 150869 := by norm_num
private theorem prime_free64SextD_152441 : Nat.Prime 152441 := by norm_num
private theorem prime_free64SextD_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_free64SextD_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_free64SextD_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_free64SextD_192263 : Nat.Prime 192263 := by norm_num
private theorem prime_free64SextD_192613 : Nat.Prime 192613 := by norm_num
private theorem prime_free64SextD_197359 : Nat.Prime 197359 := by norm_num
private theorem prime_free64SextD_204749 : Nat.Prime 204749 := by norm_num
private theorem prime_free64SextD_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_free64SextD_215447 : Nat.Prime 215447 := by norm_num
private theorem prime_free64SextD_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_free64SextD_222553 : Nat.Prime 222553 := by norm_num
private theorem prime_free64SextD_248063 : Nat.Prime 248063 := by norm_num
private theorem prime_free64SextD_255023 : Nat.Prime 255023 := by norm_num
private theorem prime_free64SextD_303713 : Nat.Prime 303713 := by norm_num
private theorem prime_free64SextD_321647 : Nat.Prime 321647 := by norm_num
private theorem prime_free64SextD_323801 : Nat.Prime 323801 := by norm_num
private theorem prime_free64SextD_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_free64SextD_387017 : Nat.Prime 387017 := by norm_num
private theorem prime_free64SextD_390499 : Nat.Prime 390499 := by norm_num
private theorem prime_free64SextD_418069 : Nat.Prime 418069 := by norm_num
private theorem prime_free64SextD_455527 : Nat.Prime 455527 := by norm_num
private theorem prime_free64SextD_472123 : Nat.Prime 472123 := by norm_num
private theorem prime_free64SextD_472831 : Nat.Prime 472831 := by norm_num
private theorem prime_free64SextD_489673 : Nat.Prime 489673 := by norm_num
private theorem prime_free64SextD_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_free64SextD_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_free64SextD_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_free64SextD_578209 : Nat.Prime 578209 := by norm_num
private theorem prime_free64SextD_590267 : Nat.Prime 590267 := by norm_num
private theorem prime_free64SextD_665591 : Nat.Prime 665591 := by norm_num
private theorem prime_free64SextD_710683 : Nat.Prime 710683 := by norm_num
private theorem prime_free64SextD_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_free64SextD_1034941 : Nat.Prime 1034941 := by norm_num
private theorem prime_free64SextD_1244879 : Nat.Prime 1244879 := by norm_num
private theorem prime_free64SextD_1260383 : Nat.Prime 1260383 := by norm_num
private theorem prime_free64SextD_1399271 : Nat.Prime 1399271 := by norm_num
private theorem prime_free64SextD_1417679 : Nat.Prime 1417679 := by norm_num
private theorem prime_free64SextD_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_free64SextD_1538233 : Nat.Prime 1538233 := by norm_num
private theorem prime_free64SextD_1741387 : Nat.Prime 1741387 := by norm_num
private theorem prime_free64SextD_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_free64SextD_1959283 : Nat.Prime 1959283 := by norm_num
private theorem prime_free64SextD_2217799 : Nat.Prime 2217799 := by norm_num
private theorem prime_free64SextD_2442113 : Nat.Prime 2442113 := by norm_num
private theorem prime_free64SextD_2712337 : Nat.Prime 2712337 := by norm_num
private theorem prime_free64SextD_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_free64SextD_2971499 : Nat.Prime 2971499 := by norm_num
private theorem prime_free64SextD_3363887 : Nat.Prime 3363887 := by norm_num
private theorem prime_free64SextD_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_free64SextD_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_free64SextD_5694119 : Nat.Prime 5694119 := by norm_num
private theorem prime_free64SextD_6618487 : Nat.Prime 6618487 := by norm_num
private theorem prime_free64SextD_7208693 : Nat.Prime 7208693 := by norm_num
private theorem prime_free64SextD_7290853 : Nat.Prime 7290853 := by norm_num
private theorem prime_free64SextD_7316849 : Nat.Prime 7316849 := by norm_num
private theorem prime_free64SextD_7819681 : Nat.Prime 7819681 := by norm_num
private theorem prime_free64SextD_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_free64SextD_8506039 : Nat.Prime 8506039 := by norm_num
private theorem prime_free64SextD_8529779 : Nat.Prime 8529779 := by norm_num
private theorem prime_free64SextD_9096713 : Nat.Prime 9096713 := by norm_num
private theorem prime_free64SextD_9181771 : Nat.Prime 9181771 := by norm_num
private theorem prime_free64SextD_9792301 : Nat.Prime 9792301 := by norm_num

private theorem prime_free64SextD_12838541 : Nat.Prime 12838541 := by
  have hfermat : (3 : ZMod 12838541) ^ (12838541 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 12838541) ^ ((12838541 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 12838541) ^ ((12838541 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 12838541) ^ ((12838541 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 12838541) ^ ((12838541 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 12838541) ^ ((12838541 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12838541 (3 : ZMod 12838541)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (11, 1), (13, 1), (67, 2)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (11, 1), (13, 1), (67, 2)] : List FactorBlock).map factorBlockValue).prod = 12838541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_15555937 : Nat.Prime 15555937 := by
  have hfermat : (5 : ZMod 15555937) ^ (15555937 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 15555937) ^ ((15555937 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 15555937) ^ ((15555937 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 15555937) ^ ((15555937 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 15555937) ^ ((15555937 - 1) / 14731) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15555937 (5 : ZMod 15555937)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (11, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (11, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod = 15555937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64SextD_14731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_40086377 : Nat.Prime 40086377 := by
  have hfermat : (3 : ZMod 40086377) ^ (40086377 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 40086377) ^ ((40086377 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 40086377) ^ ((40086377 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 40086377) ^ ((40086377 - 1) / 455527) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 40086377 (3 : ZMod 40086377)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (455527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (455527, 1)] : List FactorBlock).map factorBlockValue).prod = 40086377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64SextD_455527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_40346827 : Nat.Prime 40346827 := by
  have hfermat : (2 : ZMod 40346827) ^ (40346827 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 40346827) ^ ((40346827 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 40346827) ^ ((40346827 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 40346827) ^ ((40346827 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 40346827) ^ ((40346827 - 1) / 517267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64SextD_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_128531593 : Nat.Prime 128531593 := by
  have hfermat : (5 : ZMod 128531593) ^ (128531593 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 128531593) ^ ((128531593 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 128531593) ^ ((128531593 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 128531593) ^ ((128531593 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 128531593) ^ ((128531593 - 1) / 255023) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 128531593 (5 : ZMod 128531593)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 1), (255023, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 1), (255023, 1)] : List FactorBlock).map factorBlockValue).prod = 128531593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_255023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_171370811 : Nat.Prime 171370811 := by
  have hfermat : (2 : ZMod 171370811) ^ (171370811 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 171370811) ^ ((171370811 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 171370811) ^ ((171370811 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 171370811) ^ ((171370811 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 171370811) ^ ((171370811 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 171370811) ^ ((171370811 - 1) / 22343) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 171370811 (2 : ZMod 171370811)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (59, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (59, 1), (22343, 1)] : List FactorBlock).map factorBlockValue).prod = 171370811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_free64SextD_22343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_175593973 : Nat.Prime 175593973 := by
  have hfermat : (5 : ZMod 175593973) ^ (175593973 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 175593973) ^ ((175593973 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 175593973) ^ ((175593973 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 175593973) ^ ((175593973 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 175593973) ^ ((175593973 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 175593973) ^ ((175593973 - 1) / 5879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_free64SextD_131
      · exact prime_free64SextD_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_17678041 : Nat.Prime 17678041 := by
  have hfermat : (11 : ZMod 17678041) ^ (17678041 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 17678041) ^ ((17678041 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 17678041) ^ ((17678041 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 17678041) ^ ((17678041 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 17678041) ^ ((17678041 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 17678041) ^ ((17678041 - 1) / 823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17678041 (11 : ZMod 17678041)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (179, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (179, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod = 17678041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_179
      · exact prime_free64SextD_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_176780411 : Nat.Prime 176780411 := by
  have hfermat : (2 : ZMod 176780411) ^ (176780411 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 176780411) ^ ((176780411 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 176780411) ^ ((176780411 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 176780411) ^ ((176780411 - 1) / 17678041) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 176780411 (2 : ZMod 176780411)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17678041, 1)] : List FactorBlock).map factorBlockValue).prod = 176780411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_201386659 : Nat.Prime 201386659 := by
  have hfermat : (2 : ZMod 201386659) ^ (201386659 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 239) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 201386659) ^ ((201386659 - 1) / 751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 201386659 (2 : ZMod 201386659)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (17, 1), (239, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod = 201386659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_239
      · exact prime_t64_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_236499493 : Nat.Prime 236499493 := by
  have hfermat : (2 : ZMod 236499493) ^ (236499493 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 236499493) ^ ((236499493 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 236499493) ^ ((236499493 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 236499493) ^ ((236499493 - 1) / 2897) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 236499493) ^ ((236499493 - 1) / 6803) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 236499493 (2 : ZMod 236499493)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2897, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2897, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod = 236499493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_2897
      · exact prime_free64SextD_6803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_17885311 : Nat.Prime 17885311 := by
  have hfermat : (6 : ZMod 17885311) ^ (17885311 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 17885311) ^ ((17885311 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 17885311) ^ ((17885311 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 17885311) ^ ((17885311 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 17885311) ^ ((17885311 - 1) / 193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 17885311) ^ ((17885311 - 1) / 3089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17885311 (6 : ZMod 17885311)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (193, 1), (3089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (193, 1), (3089, 1)] : List FactorBlock).map factorBlockValue).prod = 17885311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_193
      · exact prime_free64SextD_3089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_321935599 : Nat.Prime 321935599 := by
  have hfermat : (6 : ZMod 321935599) ^ (321935599 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 321935599) ^ ((321935599 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 321935599) ^ ((321935599 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 321935599) ^ ((321935599 - 1) / 17885311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 321935599 (6 : ZMod 321935599)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17885311, 1)] : List FactorBlock).map factorBlockValue).prod = 321935599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_17885311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_370033847 : Nat.Prime 370033847 := by
  have hfermat : (5 : ZMod 370033847) ^ (370033847 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 370033847) ^ ((370033847 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 370033847) ^ ((370033847 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 370033847) ^ ((370033847 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 370033847) ^ ((370033847 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 370033847) ^ ((370033847 - 1) / 14627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 370033847 (5 : ZMod 370033847)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (139, 1), (14627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (139, 1), (14627, 1)] : List FactorBlock).map factorBlockValue).prod = 370033847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_139
      · exact prime_free64SextD_14627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_383150387 : Nat.Prime 383150387 := by
  have hfermat : (5 : ZMod 383150387) ^ (383150387 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 383150387) ^ ((383150387 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 383150387) ^ ((383150387 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 383150387) ^ ((383150387 - 1) / 2549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 383150387) ^ ((383150387 - 1) / 4421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 383150387 (5 : ZMod 383150387)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (2549, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (2549, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod = 383150387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64SextD_2549
      · exact prime_free64SextD_4421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_464968781 : Nat.Prime 464968781 := by
  have hfermat : (2 : ZMod 464968781) ^ (464968781 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 464968781) ^ ((464968781 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 464968781) ^ ((464968781 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 464968781) ^ ((464968781 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 464968781) ^ ((464968781 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 464968781) ^ ((464968781 - 1) / 1723) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 464968781 (2 : ZMod 464968781)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (103, 1), (131, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod = 464968781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_103
      · exact prime_free64SextD_131
      · exact prime_free64SextD_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_485319319 : Nat.Prime 485319319 := by
  have hfermat : (6 : ZMod 485319319) ^ (485319319 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 485319319) ^ ((485319319 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 485319319) ^ ((485319319 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 485319319) ^ ((485319319 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 485319319) ^ ((485319319 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 485319319) ^ ((485319319 - 1) / 387017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 485319319 (6 : ZMod 485319319)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (387017, 1)] : List FactorBlock).map factorBlockValue).prod = 485319319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_free64SextD_387017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_661973267 : Nat.Prime 661973267 := by
  have hfermat : (2 : ZMod 661973267) ^ (661973267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 661973267) ^ ((661973267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 661973267) ^ ((661973267 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 661973267) ^ ((661973267 - 1) / 631) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 661973267) ^ ((661973267 - 1) / 7829) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 661973267 (2 : ZMod 661973267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (67, 1), (631, 1), (7829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (67, 1), (631, 1), (7829, 1)] : List FactorBlock).map factorBlockValue).prod = 661973267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_free64SextD_631
      · exact prime_free64SextD_7829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_848810813 : Nat.Prime 848810813 := by
  have hfermat : (2 : ZMod 848810813) ^ (848810813 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 848810813) ^ ((848810813 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 848810813) ^ ((848810813 - 1) / 367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 848810813) ^ ((848810813 - 1) / 578209) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 848810813 (2 : ZMod 848810813)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (367, 1), (578209, 1)] : List FactorBlock).map factorBlockValue).prod = 848810813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_367
      · exact prime_free64SextD_578209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_222982297 : Nat.Prime 222982297 := by
  have hfermat : (10 : ZMod 222982297) ^ (222982297 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 222982297) ^ ((222982297 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 222982297) ^ ((222982297 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 222982297) ^ ((222982297 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 222982297) ^ ((222982297 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 222982297) ^ ((222982297 - 1) / 929) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 222982297 (10 : ZMod 222982297)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (73, 1), (137, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (73, 1), (137, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod = 222982297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_t64_137
      · exact prime_free64SextD_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_891929189 : Nat.Prime 891929189 := by
  have hfermat : (2 : ZMod 891929189) ^ (891929189 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 891929189) ^ ((891929189 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 891929189) ^ ((891929189 - 1) / 222982297) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 891929189 (2 : ZMod 891929189)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (222982297, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (222982297, 1)] : List FactorBlock).map factorBlockValue).prod = 891929189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_222982297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_979501163 : Nat.Prime 979501163 := by
  have hfermat : (2 : ZMod 979501163) ^ (979501163 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 979501163) ^ ((979501163 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 979501163) ^ ((979501163 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 979501163) ^ ((979501163 - 1) / 1787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 979501163) ^ ((979501163 - 1) / 5171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 979501163 (2 : ZMod 979501163)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (1787, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod = 979501163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_free64SextD_1787
      · exact prime_free64SextD_5171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_13311821 : Nat.Prime 13311821 := by
  have hfermat : (2 : ZMod 13311821) ^ (13311821 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 13311821) ^ ((13311821 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 13311821) ^ ((13311821 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 13311821) ^ ((13311821 - 1) / 665591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13311821 (2 : ZMod 13311821)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (665591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (665591, 1)] : List FactorBlock).map factorBlockValue).prod = 13311821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_665591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_2076644077 : Nat.Prime 2076644077 := by
  have hfermat : (2 : ZMod 2076644077) ^ (2076644077 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2076644077) ^ ((2076644077 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2076644077) ^ ((2076644077 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2076644077) ^ ((2076644077 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2076644077) ^ ((2076644077 - 1) / 13311821) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2076644077 (2 : ZMod 2076644077)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (13311821, 1)] : List FactorBlock).map factorBlockValue).prod = 2076644077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64SextD_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_2142115951 : Nat.Prime 2142115951 := by
  have hfermat : (3 : ZMod 2142115951) ^ (2142115951 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 2142115951) ^ ((2142115951 - 1) / 433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2142115951 (3 : ZMod 2142115951)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (13, 1), (43, 1), (59, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (13, 1), (43, 1), (59, 1), (433, 1)] : List FactorBlock).map factorBlockValue).prod = 2142115951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_43
      · exact prime_t64_59
      · exact prime_t64_433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_84294913 : Nat.Prime 84294913 := by
  have hfermat : (14 : ZMod 84294913) ^ (84294913 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 84294913) ^ ((84294913 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 84294913) ^ ((84294913 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 84294913) ^ ((84294913 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 84294913) ^ ((84294913 - 1) / 8443) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64SextD_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_3540386347 : Nat.Prime 3540386347 := by
  have hfermat : (11 : ZMod 3540386347) ^ (3540386347 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 3540386347) ^ ((3540386347 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 3540386347) ^ ((3540386347 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 3540386347) ^ ((3540386347 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 3540386347) ^ ((3540386347 - 1) / 84294913) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_3857112107 : Nat.Prime 3857112107 := by
  have hfermat : (2 : ZMod 3857112107) ^ (3857112107 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3857112107) ^ ((3857112107 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3857112107) ^ ((3857112107 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3857112107) ^ ((3857112107 - 1) / 271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3857112107) ^ ((3857112107 - 1) / 116663) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3857112107 (2 : ZMod 3857112107)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (61, 1), (271, 1), (116663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (61, 1), (271, 1), (116663, 1)] : List FactorBlock).map factorBlockValue).prod = 3857112107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_free64SextD_271
      · exact prime_free64SextD_116663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_6391408799 : Nat.Prime 6391408799 := by
  have hfermat : (23 : ZMod 6391408799) ^ (6391408799 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (23 : ZMod 6391408799) ^ ((6391408799 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (23 : ZMod 6391408799) ^ ((6391408799 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (23 : ZMod 6391408799) ^ ((6391408799 - 1) / 223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (23 : ZMod 6391408799) ^ ((6391408799 - 1) / 161017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_89
      · exact prime_t64_223
      · exact prime_free64SextD_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_7706514863 : Nat.Prime 7706514863 := by
  have hfermat : (5 : ZMod 7706514863) ^ (7706514863 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 7706514863) ^ ((7706514863 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 7706514863) ^ ((7706514863 - 1) / 1997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 7706514863) ^ ((7706514863 - 1) / 1929523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_1997
      · exact prime_free64SextD_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_8478540869 : Nat.Prime 8478540869 := by
  have hfermat : (2 : ZMod 8478540869) ^ (8478540869 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 8478540869) ^ ((8478540869 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 8478540869) ^ ((8478540869 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 8478540869) ^ ((8478540869 - 1) / 2281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 8478540869) ^ ((8478540869 - 1) / 132751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8478540869 (2 : ZMod 8478540869)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (2281, 1), (132751, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (2281, 1), (132751, 1)] : List FactorBlock).map factorBlockValue).prod = 8478540869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_2281
      · exact prime_free64SextD_132751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_9257799907 : Nat.Prime 9257799907 := by
  have hfermat : (3 : ZMod 9257799907) ^ (9257799907 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 9257799907) ^ ((9257799907 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 9257799907) ^ ((9257799907 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 9257799907) ^ ((9257799907 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 9257799907) ^ ((9257799907 - 1) / 94771) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9257799907 (3 : ZMod 9257799907)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 6), (67, 1), (94771, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 6), (67, 1), (94771, 1)] : List FactorBlock).map factorBlockValue).prod = 9257799907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_free64SextD_94771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_235217063 : Nat.Prime 235217063 := by
  have hfermat : (5 : ZMod 235217063) ^ (235217063 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 235217063) ^ ((235217063 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 235217063) ^ ((235217063 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 235217063) ^ ((235217063 - 1) / 541) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 235217063) ^ ((235217063 - 1) / 1459) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 235217063 (5 : ZMod 235217063)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (149, 1), (541, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (149, 1), (541, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod = 235217063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_149
      · exact prime_free64SextD_541
      · exact prime_free64SextD_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_9879116647 : Nat.Prime 9879116647 := by
  have hfermat : (3 : ZMod 9879116647) ^ (9879116647 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 9879116647) ^ ((9879116647 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 9879116647) ^ ((9879116647 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 9879116647) ^ ((9879116647 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 9879116647) ^ ((9879116647 - 1) / 235217063) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9879116647 (3 : ZMod 9879116647)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (235217063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (235217063, 1)] : List FactorBlock).map factorBlockValue).prod = 9879116647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_235217063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_13359593581 : Nat.Prime 13359593581 := by
  have hfermat : (2 : ZMod 13359593581) ^ (13359593581 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 13359593581) ^ ((13359593581 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 13359593581) ^ ((13359593581 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 13359593581) ^ ((13359593581 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 13359593581) ^ ((13359593581 - 1) / 2801) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 13359593581) ^ ((13359593581 - 1) / 79493) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13359593581 (2 : ZMod 13359593581)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (2801, 1), (79493, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (2801, 1), (79493, 1)] : List FactorBlock).map factorBlockValue).prod = 13359593581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_2801
      · exact prime_free64SextD_79493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_20138250467 : Nat.Prime 20138250467 := by
  have hfermat : (2 : ZMod 20138250467) ^ (20138250467 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 20138250467) ^ ((20138250467 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 20138250467) ^ ((20138250467 - 1) / 40591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 20138250467) ^ ((20138250467 - 1) / 248063) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20138250467 (2 : ZMod 20138250467)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (40591, 1), (248063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (40591, 1), (248063, 1)] : List FactorBlock).map factorBlockValue).prod = 20138250467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_40591
      · exact prime_free64SextD_248063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_10156273 : Nat.Prime 10156273 := by
  have hfermat : (11 : ZMod 10156273) ^ (10156273 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 10156273) ^ ((10156273 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 10156273) ^ ((10156273 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 10156273) ^ ((10156273 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 10156273) ^ ((10156273 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 10156273) ^ ((10156273 - 1) / 181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10156273 (11 : ZMod 10156273)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (7, 1), (167, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (7, 1), (167, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod = 10156273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_167
      · exact prime_free64SextD_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_25532870323 : Nat.Prime 25532870323 := by
  have hfermat : (2 : ZMod 25532870323) ^ (25532870323 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 25532870323) ^ ((25532870323 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 25532870323) ^ ((25532870323 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 25532870323) ^ ((25532870323 - 1) / 419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 25532870323) ^ ((25532870323 - 1) / 10156273) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25532870323 (2 : ZMod 25532870323)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (419, 1), (10156273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (419, 1), (10156273, 1)] : List FactorBlock).map factorBlockValue).prod = 25532870323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_419
      · exact prime_free64SextD_10156273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_174947471 : Nat.Prime 174947471 := by
  have hfermat : (17 : ZMod 174947471) ^ (174947471 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 174947471) ^ ((174947471 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 174947471) ^ ((174947471 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 174947471) ^ ((174947471 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 174947471) ^ ((174947471 - 1) / 472831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 174947471 (17 : ZMod 174947471)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 1), (472831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 1), (472831, 1)] : List FactorBlock).map factorBlockValue).prod = 174947471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_free64SextD_472831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_1049684827 : Nat.Prime 1049684827 := by
  have hfermat : (2 : ZMod 1049684827) ^ (1049684827 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1049684827) ^ ((1049684827 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1049684827) ^ ((1049684827 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1049684827) ^ ((1049684827 - 1) / 174947471) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1049684827 (2 : ZMod 1049684827)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (174947471, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (174947471, 1)] : List FactorBlock).map factorBlockValue).prod = 1049684827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_174947471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_29391175157 : Nat.Prime 29391175157 := by
  have hfermat : (2 : ZMod 29391175157) ^ (29391175157 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 29391175157) ^ ((29391175157 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 29391175157) ^ ((29391175157 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 29391175157) ^ ((29391175157 - 1) / 1049684827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 29391175157 (2 : ZMod 29391175157)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (1049684827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (1049684827, 1)] : List FactorBlock).map factorBlockValue).prod = 29391175157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64SextD_1049684827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_42857783 : Nat.Prime 42857783 := by
  have hfermat : (5 : ZMod 42857783) ^ (42857783 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 42857783) ^ ((42857783 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 42857783) ^ ((42857783 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 42857783) ^ ((42857783 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 42857783) ^ ((42857783 - 1) / 114593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_free64SextD_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_30429025931 : Nat.Prime 30429025931 := by
  have hfermat : (2 : ZMod 30429025931) ^ (30429025931 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 30429025931) ^ ((30429025931 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 30429025931) ^ ((30429025931 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 30429025931) ^ ((30429025931 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 30429025931) ^ ((30429025931 - 1) / 42857783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_free64SextD_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_32244294937 : Nat.Prime 32244294937 := by
  have hfermat : (10 : ZMod 32244294937) ^ (32244294937 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (10 : ZMod 32244294937) ^ ((32244294937 - 1) / 9833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_131
      · exact prime_t64_149
      · exact prime_free64SextD_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_52004916001 : Nat.Prime 52004916001 := by
  have hfermat : (7 : ZMod 52004916001) ^ (52004916001 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 52004916001) ^ ((52004916001 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 52004916001) ^ ((52004916001 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 52004916001) ^ ((52004916001 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 52004916001) ^ ((52004916001 - 1) / 53503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 52004916001 (7 : ZMod 52004916001)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 5), (5, 3), (53503, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 5), (5, 3), (53503, 1)] : List FactorBlock).map factorBlockValue).prod = 52004916001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_53503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_372958561 : Nat.Prime 372958561 := by
  have hfermat : (11 : ZMod 372958561) ^ (372958561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 372958561) ^ ((372958561 - 1) / 229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_29
      · exact prime_t64_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_55197867029 : Nat.Prime 55197867029 := by
  have hfermat : (2 : ZMod 55197867029) ^ (55197867029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 55197867029) ^ ((55197867029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 55197867029) ^ ((55197867029 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 55197867029) ^ ((55197867029 - 1) / 372958561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_free64SextD_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_59553859433 : Nat.Prime 59553859433 := by
  have hfermat : (3 : ZMod 59553859433) ^ (59553859433 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 59553859433) ^ ((59553859433 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 59553859433) ^ ((59553859433 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 59553859433) ^ ((59553859433 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 59553859433) ^ ((59553859433 - 1) / 1417679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 59553859433 (3 : ZMod 59553859433)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (59, 1), (89, 1), (1417679, 1)] : List FactorBlock).map factorBlockValue).prod = 59553859433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_89
      · exact prime_free64SextD_1417679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_52434691 : Nat.Prime 52434691 := by
  have hfermat : (3 : ZMod 52434691) ^ (52434691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 52434691) ^ ((52434691 - 1) / 22699) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 52434691 (3 : ZMod 52434691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (22699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (22699, 1)] : List FactorBlock).map factorBlockValue).prod = 52434691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64SextD_22699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_94382443801 : Nat.Prime 94382443801 := by
  have hfermat : (19 : ZMod 94382443801) ^ (94382443801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (19 : ZMod 94382443801) ^ ((94382443801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (19 : ZMod 94382443801) ^ ((94382443801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (19 : ZMod 94382443801) ^ ((94382443801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (19 : ZMod 94382443801) ^ ((94382443801 - 1) / 52434691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 94382443801 (19 : ZMod 94382443801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (5, 2), (52434691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (5, 2), (52434691, 1)] : List FactorBlock).map factorBlockValue).prod = 94382443801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_52434691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_127114246817 : Nat.Prime 127114246817 := by
  have hfermat : (3 : ZMod 127114246817) ^ (127114246817 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 127114246817) ^ ((127114246817 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 127114246817) ^ ((127114246817 - 1) / 467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 127114246817) ^ ((127114246817 - 1) / 8506039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 127114246817 (3 : ZMod 127114246817)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (467, 1), (8506039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (467, 1), (8506039, 1)] : List FactorBlock).map factorBlockValue).prod = 127114246817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_467
      · exact prime_free64SextD_8506039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_1722630643 : Nat.Prime 1722630643 := by
  have hfermat : (3 : ZMod 1722630643) ^ (1722630643 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1722630643) ^ ((1722630643 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1722630643) ^ ((1722630643 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1722630643) ^ ((1722630643 - 1) / 3449) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1722630643) ^ ((1722630643 - 1) / 83243) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1722630643 (3 : ZMod 1722630643)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3449, 1), (83243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3449, 1), (83243, 1)] : List FactorBlock).map factorBlockValue).prod = 1722630643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_3449
      · exact prime_free64SextD_83243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_172263064301 : Nat.Prime 172263064301 := by
  have hfermat : (2 : ZMod 172263064301) ^ (172263064301 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 172263064301) ^ ((172263064301 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 172263064301) ^ ((172263064301 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 172263064301) ^ ((172263064301 - 1) / 1722630643) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 172263064301 (2 : ZMod 172263064301)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (1722630643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (1722630643, 1)] : List FactorBlock).map factorBlockValue).prod = 172263064301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_1722630643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_102494143 : Nat.Prime 102494143 := by
  have hfermat : (3 : ZMod 102494143) ^ (102494143 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 102494143) ^ ((102494143 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 102494143) ^ ((102494143 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 102494143) ^ ((102494143 - 1) / 5694119) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 102494143 (3 : ZMod 102494143)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5694119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5694119, 1)] : List FactorBlock).map factorBlockValue).prod = 102494143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_5694119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_271814467237 : Nat.Prime 271814467237 := by
  have hfermat : (2 : ZMod 271814467237) ^ (271814467237 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 271814467237) ^ ((271814467237 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 271814467237) ^ ((271814467237 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 271814467237) ^ ((271814467237 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 271814467237) ^ ((271814467237 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 271814467237) ^ ((271814467237 - 1) / 102494143) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 271814467237 (2 : ZMod 271814467237)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (17, 1), (102494143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (17, 1), (102494143, 1)] : List FactorBlock).map factorBlockValue).prod = 271814467237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_free64SextD_102494143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_277508030299 : Nat.Prime 277508030299 := by
  have hfermat : (3 : ZMod 277508030299) ^ (277508030299 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 277508030299) ^ ((277508030299 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 277508030299) ^ ((277508030299 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 277508030299) ^ ((277508030299 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 277508030299) ^ ((277508030299 - 1) / 1429) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 277508030299) ^ ((277508030299 - 1) / 217223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_149
      · exact prime_free64SextD_1429
      · exact prime_free64SextD_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_9277522589 : Nat.Prime 9277522589 := by
  have hfermat : (2 : ZMod 9277522589) ^ (9277522589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9277522589) ^ ((9277522589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9277522589) ^ ((9277522589 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9277522589) ^ ((9277522589 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 9277522589) ^ ((9277522589 - 1) / 1509031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_t64_53
      · exact prime_free64SextD_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_964862349257 : Nat.Prime 964862349257 := by
  have hfermat : (5 : ZMod 964862349257) ^ (964862349257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 964862349257) ^ ((964862349257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 964862349257) ^ ((964862349257 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 964862349257) ^ ((964862349257 - 1) / 9277522589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64SextD_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_1128574980601 : Nat.Prime 1128574980601 := by
  have hfermat : (7 : ZMod 1128574980601) ^ (1128574980601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 1128574980601) ^ ((1128574980601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 1128574980601) ^ ((1128574980601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 1128574980601) ^ ((1128574980601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 1128574980601) ^ ((1128574980601 - 1) / 13009) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 1128574980601) ^ ((1128574980601 - 1) / 144589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1128574980601 (7 : ZMod 1128574980601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (13009, 1), (144589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (13009, 1), (144589, 1)] : List FactorBlock).map factorBlockValue).prod = 1128574980601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_13009
      · exact prime_free64SextD_144589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_1694722097147 : Nat.Prime 1694722097147 := by
  have hfermat : (2 : ZMod 1694722097147) ^ (1694722097147 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1694722097147) ^ ((1694722097147 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1694722097147) ^ ((1694722097147 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1694722097147) ^ ((1694722097147 - 1) / 62981) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1694722097147) ^ ((1694722097147 - 1) / 1034941) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1694722097147 (2 : ZMod 1694722097147)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (62981, 1), (1034941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (62981, 1), (1034941, 1)] : List FactorBlock).map factorBlockValue).prod = 1694722097147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64SextD_62981
      · exact prime_free64SextD_1034941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_1898100541591 : Nat.Prime 1898100541591 := by
  have hfermat : (3 : ZMod 1898100541591) ^ (1898100541591 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 1433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 1898100541591) ^ ((1898100541591 - 1) / 8783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64SextD_457
      · exact prime_free64SextD_1433
      · exact prime_free64SextD_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_217049968777 : Nat.Prime 217049968777 := by
  have hfermat : (7 : ZMod 217049968777) ^ (217049968777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 217049968777) ^ ((217049968777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 217049968777) ^ ((217049968777 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 217049968777) ^ ((217049968777 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 217049968777) ^ ((217049968777 - 1) / 907) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 217049968777) ^ ((217049968777 - 1) / 321647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 217049968777 (7 : ZMod 217049968777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (31, 1), (907, 1), (321647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (31, 1), (907, 1), (321647, 1)] : List FactorBlock).map factorBlockValue).prod = 217049968777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_free64SextD_907
      · exact prime_free64SextD_321647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_2170499687771 : Nat.Prime 2170499687771 := by
  have hfermat : (2 : ZMod 2170499687771) ^ (2170499687771 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2170499687771) ^ ((2170499687771 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2170499687771) ^ ((2170499687771 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2170499687771) ^ ((2170499687771 - 1) / 217049968777) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2170499687771 (2 : ZMod 2170499687771)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (217049968777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (217049968777, 1)] : List FactorBlock).map factorBlockValue).prod = 2170499687771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_217049968777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_3115755898081 : Nat.Prime 3115755898081 := by
  have hfermat : (13 : ZMod 3115755898081) ^ (3115755898081 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 15887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (13 : ZMod 3115755898081) ^ ((3115755898081 - 1) / 58369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3115755898081 (13 : ZMod 3115755898081)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (7, 1), (15887, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (7, 1), (15887, 1), (58369, 1)] : List FactorBlock).map factorBlockValue).prod = 3115755898081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64SextD_15887
      · exact prime_free64SextD_58369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_16905180671 : Nat.Prime 16905180671 := by
  have hfermat : (7 : ZMod 16905180671) ^ (16905180671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 16905180671) ^ ((16905180671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 16905180671) ^ ((16905180671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 16905180671) ^ ((16905180671 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 16905180671) ^ ((16905180671 - 1) / 157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 16905180671) ^ ((16905180671 - 1) / 1538233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16905180671 (7 : ZMod 16905180671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (157, 1), (1538233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (157, 1), (1538233, 1)] : List FactorBlock).map factorBlockValue).prod = 16905180671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_157
      · exact prime_free64SextD_1538233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_5206795646669 : Nat.Prime 5206795646669 := by
  have hfermat : (2 : ZMod 5206795646669) ^ (5206795646669 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5206795646669) ^ ((5206795646669 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5206795646669) ^ ((5206795646669 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5206795646669) ^ ((5206795646669 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5206795646669) ^ ((5206795646669 - 1) / 16905180671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5206795646669 (2 : ZMod 5206795646669)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (16905180671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (16905180671, 1)] : List FactorBlock).map factorBlockValue).prod = 5206795646669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64SextD_16905180671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_198824849 : Nat.Prime 198824849 := by
  have hfermat : (3 : ZMod 198824849) ^ (198824849 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 198824849) ^ ((198824849 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 198824849) ^ ((198824849 - 1) / 2113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 198824849) ^ ((198824849 - 1) / 5881) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 198824849 (3 : ZMod 198824849)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (2113, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (2113, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod = 198824849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_2113
      · exact prime_free64SextD_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_11755320372277 : Nat.Prime 11755320372277 := by
  have hfermat : (6 : ZMod 11755320372277) ^ (11755320372277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 11755320372277) ^ ((11755320372277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 11755320372277) ^ ((11755320372277 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 11755320372277) ^ ((11755320372277 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 11755320372277) ^ ((11755320372277 - 1) / 379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 11755320372277) ^ ((11755320372277 - 1) / 198824849) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11755320372277 (6 : ZMod 11755320372277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (13, 1), (379, 1), (198824849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (13, 1), (379, 1), (198824849, 1)] : List FactorBlock).map factorBlockValue).prod = 11755320372277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64SextD_379
      · exact prime_free64SextD_198824849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_45240499 : Nat.Prime 45240499 := by
  have hfermat : (2 : ZMod 45240499) ^ (45240499 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 45240499) ^ ((45240499 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 45240499) ^ ((45240499 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 45240499) ^ ((45240499 - 1) / 641) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 45240499) ^ ((45240499 - 1) / 1307) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 45240499 (2 : ZMod 45240499)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (641, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (641, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod = 45240499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_641
      · exact prime_free64SextD_1307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_180961997 : Nat.Prime 180961997 := by
  have hfermat : (2 : ZMod 180961997) ^ (180961997 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 180961997) ^ ((180961997 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 180961997) ^ ((180961997 - 1) / 45240499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 180961997 (2 : ZMod 180961997)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (45240499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (45240499, 1)] : List FactorBlock).map factorBlockValue).prod = 180961997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_45240499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_16373441488561 : Nat.Prime 16373441488561 := by
  have hfermat : (14 : ZMod 16373441488561) ^ (16373441488561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (14 : ZMod 16373441488561) ^ ((16373441488561 - 1) / 180961997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16373441488561 (14 : ZMod 16373441488561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (13, 1), (29, 1), (180961997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (13, 1), (29, 1), (180961997, 1)] : List FactorBlock).map factorBlockValue).prod = 16373441488561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_29
      · exact prime_free64SextD_180961997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_17840236707533 : Nat.Prime 17840236707533 := by
  have hfermat : (2 : ZMod 17840236707533) ^ (17840236707533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 751) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 17840236707533) ^ ((17840236707533 - 1) / 1619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17840236707533 (2 : ZMod 17840236707533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (59, 1), (79, 1), (751, 1), (787, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (59, 1), (79, 1), (751, 1), (787, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod = 17840236707533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_79
      · exact prime_t64_751
      · exact prime_t64_787
      · exact prime_t64_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_61600871 : Nat.Prime 61600871 := by
  have hfermat : (13 : ZMod 61600871) ^ (61600871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 61600871) ^ ((61600871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 61600871) ^ ((61600871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 61600871) ^ ((61600871 - 1) / 647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 61600871) ^ ((61600871 - 1) / 9521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 61600871 (13 : ZMod 61600871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (647, 1), (9521, 1)] : List FactorBlock).map factorBlockValue).prod = 61600871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_647
      · exact prime_free64SextD_9521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_5225601886931 : Nat.Prime 5225601886931 := by
  have hfermat : (2 : ZMod 5225601886931) ^ (5225601886931 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5225601886931) ^ ((5225601886931 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5225601886931) ^ ((5225601886931 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5225601886931) ^ ((5225601886931 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5225601886931) ^ ((5225601886931 - 1) / 499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 5225601886931) ^ ((5225601886931 - 1) / 61600871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5225601886931 (2 : ZMod 5225601886931)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (499, 1), (61600871, 1)] : List FactorBlock).map factorBlockValue).prod = 5225601886931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_499
      · exact prime_free64SextD_61600871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_31353611321587 : Nat.Prime 31353611321587 := by
  have hfermat : (2 : ZMod 31353611321587) ^ (31353611321587 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 31353611321587) ^ ((31353611321587 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 31353611321587) ^ ((31353611321587 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 31353611321587) ^ ((31353611321587 - 1) / 5225601886931) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 31353611321587 (2 : ZMod 31353611321587)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5225601886931, 1)] : List FactorBlock).map factorBlockValue).prod = 31353611321587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_5225601886931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_166895539 : Nat.Prime 166895539 := by
  have hfermat : (2 : ZMod 166895539) ^ (166895539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 166895539) ^ ((166895539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 166895539) ^ ((166895539 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 166895539) ^ ((166895539 - 1) / 1873) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 166895539) ^ ((166895539 - 1) / 14851) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 166895539 (2 : ZMod 166895539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1873, 1), (14851, 1)] : List FactorBlock).map factorBlockValue).prod = 166895539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_1873
      · exact prime_free64SextD_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_33484585780649 : Nat.Prime 33484585780649 := by
  have hfermat : (3 : ZMod 33484585780649) ^ (33484585780649 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 33484585780649) ^ ((33484585780649 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 33484585780649) ^ ((33484585780649 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 33484585780649) ^ ((33484585780649 - 1) / 809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 33484585780649) ^ ((33484585780649 - 1) / 166895539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 33484585780649 (3 : ZMod 33484585780649)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (809, 1), (166895539, 1)] : List FactorBlock).map factorBlockValue).prod = 33484585780649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64SextD_809
      · exact prime_free64SextD_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_52107281 : Nat.Prime 52107281 := by
  have hfermat : (3 : ZMod 52107281) ^ (52107281 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 52107281) ^ ((52107281 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 52107281) ^ ((52107281 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 52107281) ^ ((52107281 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 52107281) ^ ((52107281 - 1) / 21011) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 52107281 (3 : ZMod 52107281)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (31, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (31, 1), (21011, 1)] : List FactorBlock).map factorBlockValue).prod = 52107281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_free64SextD_21011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_39117456919511 : Nat.Prime 39117456919511 := by
  have hfermat : (17 : ZMod 39117456919511) ^ (39117456919511 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 39117456919511) ^ ((39117456919511 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 39117456919511) ^ ((39117456919511 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 39117456919511) ^ ((39117456919511 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 39117456919511) ^ ((39117456919511 - 1) / 1831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 39117456919511) ^ ((39117456919511 - 1) / 52107281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 39117456919511 (17 : ZMod 39117456919511)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (41, 1), (1831, 1), (52107281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (41, 1), (1831, 1), (52107281, 1)] : List FactorBlock).map factorBlockValue).prod = 39117456919511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_free64SextD_1831
      · exact prime_free64SextD_52107281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_1379120367743 : Nat.Prime 1379120367743 := by
  have hfermat : (5 : ZMod 1379120367743) ^ (1379120367743 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1379120367743) ^ ((1379120367743 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1379120367743) ^ ((1379120367743 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1379120367743) ^ ((1379120367743 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 1379120367743) ^ ((1379120367743 - 1) / 109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 1379120367743) ^ ((1379120367743 - 1) / 9181771) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1379120367743 (5 : ZMod 1379120367743)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (53, 1), (109, 1), (9181771, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (53, 1), (109, 1), (9181771, 1)] : List FactorBlock).map factorBlockValue).prod = 1379120367743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_53
      · exact prime_t64_109
      · exact prime_free64SextD_9181771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_44131851767777 : Nat.Prime 44131851767777 := by
  have hfermat : (3 : ZMod 44131851767777) ^ (44131851767777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 44131851767777) ^ ((44131851767777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 44131851767777) ^ ((44131851767777 - 1) / 1379120367743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 44131851767777 (3 : ZMod 44131851767777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (1379120367743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (1379120367743, 1)] : List FactorBlock).map factorBlockValue).prod = 44131851767777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_1379120367743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_75391139 : Nat.Prime 75391139 := by
  have hfermat : (2 : ZMod 75391139) ^ (75391139 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 75391139) ^ ((75391139 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 75391139) ^ ((75391139 - 1) / 191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 75391139) ^ ((75391139 - 1) / 197359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 75391139 (2 : ZMod 75391139)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (191, 1), (197359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (191, 1), (197359, 1)] : List FactorBlock).map factorBlockValue).prod = 75391139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_191
      · exact prime_free64SextD_197359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_71425565088601 : Nat.Prime 71425565088601 := by
  have hfermat : (21 : ZMod 71425565088601) ^ (71425565088601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (21 : ZMod 71425565088601) ^ ((71425565088601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (21 : ZMod 71425565088601) ^ ((71425565088601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (21 : ZMod 71425565088601) ^ ((71425565088601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (21 : ZMod 71425565088601) ^ ((71425565088601 - 1) / 1579) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (21 : ZMod 71425565088601) ^ ((71425565088601 - 1) / 75391139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 71425565088601 (21 : ZMod 71425565088601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (1579, 1), (75391139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (1579, 1), (75391139, 1)] : List FactorBlock).map factorBlockValue).prod = 71425565088601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_1579
      · exact prime_free64SextD_75391139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_2703815077 : Nat.Prime 2703815077 := by
  have hfermat : (2 : ZMod 2703815077) ^ (2703815077 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2703815077) ^ ((2703815077 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2703815077) ^ ((2703815077 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2703815077) ^ ((2703815077 - 1) / 577) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2703815077) ^ ((2703815077 - 1) / 390499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2703815077 (2 : ZMod 2703815077)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (577, 1), (390499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (577, 1), (390499, 1)] : List FactorBlock).map factorBlockValue).prod = 2703815077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_577
      · exact prime_free64SextD_390499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_80919777624457 : Nat.Prime 80919777624457 := by
  have hfermat : (5 : ZMod 80919777624457) ^ (80919777624457 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 80919777624457) ^ ((80919777624457 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 80919777624457) ^ ((80919777624457 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 80919777624457) ^ ((80919777624457 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 80919777624457) ^ ((80919777624457 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 80919777624457) ^ ((80919777624457 - 1) / 2703815077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 80919777624457 (5 : ZMod 80919777624457)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (29, 1), (43, 1), (2703815077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (29, 1), (43, 1), (2703815077, 1)] : List FactorBlock).map factorBlockValue).prod = 80919777624457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_t64_43
      · exact prime_free64SextD_2703815077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_323679110497829 : Nat.Prime 323679110497829 := by
  have hfermat : (2 : ZMod 323679110497829) ^ (323679110497829 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 323679110497829) ^ ((323679110497829 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 323679110497829) ^ ((323679110497829 - 1) / 80919777624457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 323679110497829 (2 : ZMod 323679110497829)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (80919777624457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (80919777624457, 1)] : List FactorBlock).map factorBlockValue).prod = 323679110497829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_80919777624457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_415873863425473 : Nat.Prime 415873863425473 := by
  have hfermat : (7 : ZMod 415873863425473) ^ (415873863425473 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 463) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 415873863425473) ^ ((415873863425473 - 1) / 97157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 415873863425473 (7 : ZMod 415873863425473)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (179, 1), (269, 1), (463, 1), (97157, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (179, 1), (269, 1), (463, 1), (97157, 1)] : List FactorBlock).map factorBlockValue).prod = 415873863425473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_179
      · exact prime_t64_269
      · exact prime_free64SextD_463
      · exact prime_free64SextD_97157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_14166409 : Nat.Prime 14166409 := by
  have hfermat : (7 : ZMod 14166409) ^ (14166409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 14166409) ^ ((14166409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 14166409) ^ ((14166409 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 14166409) ^ ((14166409 - 1) / 590267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14166409 (7 : ZMod 14166409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (590267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (590267, 1)] : List FactorBlock).map factorBlockValue).prod = 14166409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_590267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_869490835208461 : Nat.Prime 869490835208461 := by
  have hfermat : (6 : ZMod 869490835208461) ^ (869490835208461 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 869490835208461) ^ ((869490835208461 - 1) / 14166409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 869490835208461 (6 : ZMod 869490835208461)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 5), (5, 1), (73, 1), (173, 1), (14166409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 5), (5, 1), (73, 1), (173, 1), (14166409, 1)] : List FactorBlock).map factorBlockValue).prod = 869490835208461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_73
      · exact prime_free64SextD_173
      · exact prime_free64SextD_14166409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_1565701635647021 : Nat.Prime 1565701635647021 := by
  have hfermat : (2 : ZMod 1565701635647021) ^ (1565701635647021 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 2099) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 1565701635647021) ^ ((1565701635647021 - 1) / 105769) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1565701635647021 (2 : ZMod 1565701635647021)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (19, 1), (67, 1), (277, 1), (2099, 1), (105769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (19, 1), (67, 1), (277, 1), (2099, 1), (105769, 1)] : List FactorBlock).map factorBlockValue).prod = 1565701635647021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_67
      · exact prime_free64SextD_277
      · exact prime_free64SextD_2099
      · exact prime_free64SextD_105769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_4762488116064271 : Nat.Prime 4762488116064271 := by
  have hfermat : (3 : ZMod 4762488116064271) ^ (4762488116064271 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 472123) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 4762488116064271) ^ ((4762488116064271 - 1) / 7819681) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4762488116064271 (3 : ZMod 4762488116064271)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (43, 1), (472123, 1), (7819681, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (43, 1), (472123, 1), (7819681, 1)] : List FactorBlock).map factorBlockValue).prod = 4762488116064271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_free64SextD_472123
      · exact prime_free64SextD_7819681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_8819756234269 : Nat.Prime 8819756234269 := by
  have hfermat : (2 : ZMod 8819756234269) ^ (8819756234269 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 8819756234269) ^ ((8819756234269 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 8819756234269) ^ ((8819756234269 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 8819756234269) ^ ((8819756234269 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 8819756234269) ^ ((8819756234269 - 1) / 75037) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 8819756234269) ^ ((8819756234269 - 1) / 1399271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8819756234269 (2 : ZMod 8819756234269)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (75037, 1), (1399271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (75037, 1), (1399271, 1)] : List FactorBlock).map factorBlockValue).prod = 8819756234269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_75037
      · exact prime_free64SextD_1399271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_1322963435140351 : Nat.Prime 1322963435140351 := by
  have hfermat : (6 : ZMod 1322963435140351) ^ (1322963435140351 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1322963435140351) ^ ((1322963435140351 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1322963435140351) ^ ((1322963435140351 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1322963435140351) ^ ((1322963435140351 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1322963435140351) ^ ((1322963435140351 - 1) / 8819756234269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1322963435140351 (6 : ZMod 1322963435140351)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (8819756234269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (8819756234269, 1)] : List FactorBlock).map factorBlockValue).prod = 1322963435140351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_8819756234269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_7937780610842107 : Nat.Prime 7937780610842107 := by
  have hfermat : (2 : ZMod 7937780610842107) ^ (7937780610842107 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7937780610842107) ^ ((7937780610842107 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7937780610842107) ^ ((7937780610842107 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7937780610842107) ^ ((7937780610842107 - 1) / 1322963435140351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7937780610842107 (2 : ZMod 7937780610842107)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1322963435140351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1322963435140351, 1)] : List FactorBlock).map factorBlockValue).prod = 7937780610842107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_1322963435140351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_9811689499 : Nat.Prime 9811689499 := by
  have hfermat : (3 : ZMod 9811689499) ^ (9811689499 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 9811689499) ^ ((9811689499 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 9811689499) ^ ((9811689499 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 9811689499) ^ ((9811689499 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 9811689499) ^ ((9811689499 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 9811689499) ^ ((9811689499 - 1) / 710683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9811689499 (3 : ZMod 9811689499)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (59, 1), (710683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (59, 1), (710683, 1)] : List FactorBlock).map factorBlockValue).prod = 9811689499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_free64SextD_710683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_8551005138652489 : Nat.Prime 8551005138652489 := by
  have hfermat : (13 : ZMod 8551005138652489) ^ (8551005138652489 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 8551005138652489) ^ ((8551005138652489 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 8551005138652489) ^ ((8551005138652489 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 8551005138652489) ^ ((8551005138652489 - 1) / 36313) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 8551005138652489) ^ ((8551005138652489 - 1) / 9811689499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8551005138652489 (13 : ZMod 8551005138652489)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (36313, 1), (9811689499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (36313, 1), (9811689499, 1)] : List FactorBlock).map factorBlockValue).prod = 8551005138652489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_36313
      · exact prime_free64SextD_9811689499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_910838081 : Nat.Prime 910838081 := by
  have hfermat : (3 : ZMod 910838081) ^ (910838081 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 910838081) ^ ((910838081 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 910838081) ^ ((910838081 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 910838081) ^ ((910838081 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 910838081) ^ ((910838081 - 1) / 16453) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_173
      · exact prime_free64SextD_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_75763511577581 : Nat.Prime 75763511577581 := by
  have hfermat : (3 : ZMod 75763511577581) ^ (75763511577581 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 75763511577581) ^ ((75763511577581 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 75763511577581) ^ ((75763511577581 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 75763511577581) ^ ((75763511577581 - 1) / 4159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 75763511577581) ^ ((75763511577581 - 1) / 910838081) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_4159
      · exact prime_free64SextD_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_17274080639688469 : Nat.Prime 17274080639688469 := by
  have hfermat : (2 : ZMod 17274080639688469) ^ (17274080639688469 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 17274080639688469) ^ ((17274080639688469 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 17274080639688469) ^ ((17274080639688469 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 17274080639688469) ^ ((17274080639688469 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 17274080639688469) ^ ((17274080639688469 - 1) / 75763511577581) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_free64SextD_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_31865583647 : Nat.Prime 31865583647 := by
  have hfermat : (5 : ZMod 31865583647) ^ (31865583647 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 31865583647) ^ ((31865583647 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 31865583647) ^ ((31865583647 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 31865583647) ^ ((31865583647 - 1) / 5507) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 31865583647) ^ ((31865583647 - 1) / 222553) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 31865583647 (5 : ZMod 31865583647)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (5507, 1), (222553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (5507, 1), (222553, 1)] : List FactorBlock).map factorBlockValue).prod = 31865583647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64SextD_5507
      · exact prime_free64SextD_222553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_16060254158089 : Nat.Prime 16060254158089 := by
  have hfermat : (13 : ZMod 16060254158089) ^ (16060254158089 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 16060254158089) ^ ((16060254158089 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 16060254158089) ^ ((16060254158089 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 16060254158089) ^ ((16060254158089 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 16060254158089) ^ ((16060254158089 - 1) / 31865583647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16060254158089 (13 : ZMod 16060254158089)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 1), (31865583647, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 1), (31865583647, 1)] : List FactorBlock).map factorBlockValue).prod = 16060254158089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64SextD_31865583647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_25246719536515909 : Nat.Prime 25246719536515909 := by
  have hfermat : (2 : ZMod 25246719536515909) ^ (25246719536515909 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 25246719536515909) ^ ((25246719536515909 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 25246719536515909) ^ ((25246719536515909 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 25246719536515909) ^ ((25246719536515909 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 25246719536515909) ^ ((25246719536515909 - 1) / 16060254158089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25246719536515909 (2 : ZMod 25246719536515909)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (131, 1), (16060254158089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (131, 1), (16060254158089, 1)] : List FactorBlock).map factorBlockValue).prod = 25246719536515909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_131
      · exact prime_free64SextD_16060254158089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_27238268144131903 : Nat.Prime 27238268144131903 := by
  have hfermat : (3 : ZMod 27238268144131903) ^ (27238268144131903 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 82529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 27238268144131903) ^ ((27238268144131903 - 1) / 1244879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 27238268144131903 (3 : ZMod 27238268144131903)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (13, 1), (103, 1), (82529, 1), (1244879, 1)] : List FactorBlock).map factorBlockValue).prod = 27238268144131903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_103
      · exact prime_free64SextD_82529
      · exact prime_free64SextD_1244879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_14999741 : Nat.Prime 14999741 := by
  have hfermat : (3 : ZMod 14999741) ^ (14999741 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 14999741) ^ ((14999741 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 14999741) ^ ((14999741 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 14999741) ^ ((14999741 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 14999741) ^ ((14999741 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 14999741) ^ ((14999741 - 1) / 5639) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14999741 (3 : ZMod 14999741)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (19, 1), (5639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (19, 1), (5639, 1)] : List FactorBlock).map factorBlockValue).prod = 14999741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_free64SextD_5639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_11655978276633277 : Nat.Prime 11655978276633277 := by
  have hfermat : (2 : ZMod 11655978276633277) ^ (11655978276633277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 81047) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 11655978276633277) ^ ((11655978276633277 - 1) / 14999741) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_47
      · exact prime_free64SextD_81047
      · exact prime_free64SextD_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_116559782766332771 : Nat.Prime 116559782766332771 := by
  have hfermat : (2 : ZMod 116559782766332771) ^ (116559782766332771 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 116559782766332771) ^ ((116559782766332771 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 116559782766332771) ^ ((116559782766332771 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 116559782766332771) ^ ((116559782766332771 - 1) / 11655978276633277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_11641387 : Nat.Prime 11641387 := by
  have hfermat : (3 : ZMod 11641387) ^ (11641387 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11641387) ^ ((11641387 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11641387) ^ ((11641387 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11641387) ^ ((11641387 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11641387) ^ ((11641387 - 1) / 18133) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11641387 (3 : ZMod 11641387)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (107, 1), (18133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (107, 1), (18133, 1)] : List FactorBlock).map factorBlockValue).prod = 11641387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_107
      · exact prime_free64SextD_18133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_318927438253 : Nat.Prime 318927438253 := by
  have hfermat : (5 : ZMod 318927438253) ^ (318927438253 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 318927438253) ^ ((318927438253 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 318927438253) ^ ((318927438253 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 318927438253) ^ ((318927438253 - 1) / 761) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 318927438253) ^ ((318927438253 - 1) / 11641387) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 318927438253 (5 : ZMod 318927438253)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (761, 1), (11641387, 1)] : List FactorBlock).map factorBlockValue).prod = 318927438253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_761
      · exact prime_free64SextD_11641387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_157435978474087427 : Nat.Prime 157435978474087427 := by
  have hfermat : (2 : ZMod 157435978474087427) ^ (157435978474087427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 157435978474087427) ^ ((157435978474087427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 157435978474087427) ^ ((157435978474087427 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 157435978474087427) ^ ((157435978474087427 - 1) / 4657) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 157435978474087427) ^ ((157435978474087427 - 1) / 318927438253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 157435978474087427 (2 : ZMod 157435978474087427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (4657, 1), (318927438253, 1)] : List FactorBlock).map factorBlockValue).prod = 157435978474087427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_free64SextD_4657
      · exact prime_free64SextD_318927438253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_579848016567285199 : Nat.Prime 579848016567285199 := by
  have hfermat : (3 : ZMod 579848016567285199) ^ (579848016567285199 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 579848016567285199) ^ ((579848016567285199 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 579848016567285199) ^ ((579848016567285199 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 579848016567285199) ^ ((579848016567285199 - 1) / 10531) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 579848016567285199) ^ ((579848016567285199 - 1) / 418069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 579848016567285199) ^ ((579848016567285199 - 1) / 7316849) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 579848016567285199 (3 : ZMod 579848016567285199)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (10531, 1), (418069, 1), (7316849, 1)] : List FactorBlock).map factorBlockValue).prod = 579848016567285199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_10531
      · exact prime_free64SextD_418069
      · exact prime_free64SextD_7316849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_74000153 : Nat.Prime 74000153 := by
  have hfermat : (3 : ZMod 74000153) ^ (74000153 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 74000153) ^ ((74000153 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 74000153) ^ ((74000153 - 1) / 2297) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 74000153) ^ ((74000153 - 1) / 4027) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 74000153 (3 : ZMod 74000153)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (2297, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (2297, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod = 74000153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_2297
      · exact prime_free64SextD_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_859116819482400139 : Nat.Prime 859116819482400139 := by
  have hfermat : (2 : ZMod 859116819482400139) ^ (859116819482400139 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 22943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 859116819482400139) ^ ((859116819482400139 - 1) / 74000153) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 859116819482400139 (2 : ZMod 859116819482400139)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (17, 1), (41, 1), (22943, 1), (74000153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (17, 1), (41, 1), (22943, 1), (74000153, 1)] : List FactorBlock).map factorBlockValue).prod = 859116819482400139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_free64SextD_22943
      · exact prime_free64SextD_74000153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_1466977702710658571 : Nat.Prime 1466977702710658571 := by
  have hfermat : (2 : ZMod 1466977702710658571) ^ (1466977702710658571 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 6911) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 8377) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 46649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 1466977702710658571) ^ ((1466977702710658571 - 1) / 54319) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1466977702710658571 (2 : ZMod 1466977702710658571)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (6911, 1), (8377, 1), (46649, 1), (54319, 1)] : List FactorBlock).map factorBlockValue).prod = 1466977702710658571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_6911
      · exact prime_free64SextD_8377
      · exact prime_free64SextD_46649
      · exact prime_free64SextD_54319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_69769875117036373 : Nat.Prime 69769875117036373 := by
  have hfermat : (5 : ZMod 69769875117036373) ^ (69769875117036373 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 69769875117036373) ^ ((69769875117036373 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 69769875117036373) ^ ((69769875117036373 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 69769875117036373) ^ ((69769875117036373 - 1) / 2713) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 69769875117036373) ^ ((69769875117036373 - 1) / 323801) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 69769875117036373) ^ ((69769875117036373 - 1) / 6618487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 69769875117036373 (5 : ZMod 69769875117036373)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2713, 1), (323801, 1), (6618487, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2713, 1), (323801, 1), (6618487, 1)] : List FactorBlock).map factorBlockValue).prod = 69769875117036373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_2713
      · exact prime_free64SextD_323801
      · exact prime_free64SextD_6618487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_12000418520130256157 : Nat.Prime 12000418520130256157 := by
  have hfermat : (2 : ZMod 12000418520130256157) ^ (12000418520130256157 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12000418520130256157) ^ ((12000418520130256157 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12000418520130256157) ^ ((12000418520130256157 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12000418520130256157) ^ ((12000418520130256157 - 1) / 69769875117036373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12000418520130256157 (2 : ZMod 12000418520130256157)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (43, 1), (69769875117036373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (43, 1), (69769875117036373, 1)] : List FactorBlock).map factorBlockValue).prod = 12000418520130256157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_free64SextD_69769875117036373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_106750482823 : Nat.Prime 106750482823 := by
  have hfermat : (3 : ZMod 106750482823) ^ (106750482823 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 106750482823) ^ ((106750482823 - 1) / 21683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 106750482823 (3 : ZMod 106750482823)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (17, 1), (31, 1), (173, 1), (21683, 1)] : List FactorBlock).map factorBlockValue).prod = 106750482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_31
      · exact prime_free64SextD_173
      · exact prime_free64SextD_21683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_137647879701195599473 : Nat.Prime 137647879701195599473 := by
  have hfermat : (5 : ZMod 137647879701195599473) ^ (137647879701195599473 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 137647879701195599473) ^ ((137647879701195599473 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 137647879701195599473) ^ ((137647879701195599473 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 137647879701195599473) ^ ((137647879701195599473 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 137647879701195599473) ^ ((137647879701195599473 - 1) / 2442113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 137647879701195599473) ^ ((137647879701195599473 - 1) / 106750482823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 137647879701195599473 (5 : ZMod 137647879701195599473)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (11, 1), (2442113, 1), (106750482823, 1)] : List FactorBlock).map factorBlockValue).prod = 137647879701195599473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64SextD_2442113
      · exact prime_free64SextD_106750482823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_14615833261 : Nat.Prime 14615833261 := by
  have hfermat : (6 : ZMod 14615833261) ^ (14615833261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 14615833261) ^ ((14615833261 - 1) / 192263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14615833261 (6 : ZMod 14615833261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (7, 1), (181, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod = 14615833261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64SextD_181
      · exact prime_free64SextD_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_175389999133 : Nat.Prime 175389999133 := by
  have hfermat : (2 : ZMod 175389999133) ^ (175389999133 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 175389999133) ^ ((175389999133 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 175389999133) ^ ((175389999133 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 175389999133) ^ ((175389999133 - 1) / 14615833261) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 175389999133 (2 : ZMod 175389999133)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (14615833261, 1)] : List FactorBlock).map factorBlockValue).prod = 175389999133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_14615833261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_1052339994799 : Nat.Prime 1052339994799 := by
  have hfermat : (6 : ZMod 1052339994799) ^ (1052339994799 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1052339994799) ^ ((1052339994799 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1052339994799) ^ ((1052339994799 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1052339994799) ^ ((1052339994799 - 1) / 175389999133) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1052339994799 (6 : ZMod 1052339994799)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (175389999133, 1)] : List FactorBlock).map factorBlockValue).prod = 1052339994799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_175389999133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_138104211745804923847 : Nat.Prime 138104211745804923847 := by
  have hfermat : (5 : ZMod 138104211745804923847) ^ (138104211745804923847 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 138104211745804923847) ^ ((138104211745804923847 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 138104211745804923847) ^ ((138104211745804923847 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 138104211745804923847) ^ ((138104211745804923847 - 1) / 7290853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 138104211745804923847) ^ ((138104211745804923847 - 1) / 1052339994799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 138104211745804923847 (5 : ZMod 138104211745804923847)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (7290853, 1), (1052339994799, 1)] : List FactorBlock).map factorBlockValue).prod = 138104211745804923847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_7290853
      · exact prime_free64SextD_1052339994799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_123638071 : Nat.Prime 123638071 := by
  have hfermat : (7 : ZMod 123638071) ^ (123638071 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 123638071) ^ ((123638071 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 123638071) ^ ((123638071 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 123638071) ^ ((123638071 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 123638071) ^ ((123638071 - 1) / 4121269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64SextD_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_741828427 : Nat.Prime 741828427 := by
  have hfermat : (2 : ZMod 741828427) ^ (741828427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 741828427) ^ ((741828427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 741828427) ^ ((741828427 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 741828427) ^ ((741828427 - 1) / 123638071) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  have hfermat : (2 : ZMod 429449525106920937499) ^ (429449525106920937499 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 5449) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 8089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 429449525106920937499) ^ ((429449525106920937499 - 1) / 741828427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64SextD_199
      · exact prime_free64SextD_5449
      · exact prime_free64SextD_8089
      · exact prime_free64SextD_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6

private theorem prime_free64SextD_1136223397 : Nat.Prime 1136223397 := by
  have hfermat : (5 : ZMod 1136223397) ^ (1136223397 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1136223397) ^ ((1136223397 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1136223397) ^ ((1136223397 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1136223397) ^ ((1136223397 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 1136223397) ^ ((1136223397 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 1136223397) ^ ((1136223397 - 1) / 12421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1136223397 (5 : ZMod 1136223397)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (7, 1), (11, 2), (12421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (7, 1), (11, 2), (12421, 1)] : List FactorBlock).map factorBlockValue).prod = 1136223397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64SextD_12421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_4544893589 : Nat.Prime 4544893589 := by
  have hfermat : (2 : ZMod 4544893589) ^ (4544893589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4544893589) ^ ((4544893589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4544893589) ^ ((4544893589 - 1) / 1136223397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4544893589 (2 : ZMod 4544893589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1136223397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1136223397, 1)] : List FactorBlock).map factorBlockValue).prod = 4544893589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_1136223397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_355492486744403 : Nat.Prime 355492486744403 := by
  have hfermat : (5 : ZMod 355492486744403) ^ (355492486744403 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 355492486744403) ^ ((355492486744403 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 355492486744403) ^ ((355492486744403 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 355492486744403) ^ ((355492486744403 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 355492486744403) ^ ((355492486744403 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 355492486744403) ^ ((355492486744403 - 1) / 4544893589) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 355492486744403 (5 : ZMod 355492486744403)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (37, 1), (151, 1), (4544893589, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (37, 1), (151, 1), (4544893589, 1)] : List FactorBlock).map factorBlockValue).prod = 355492486744403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_free64SextD_151
      · exact prime_free64SextD_4544893589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_481685209688931176941 : Nat.Prime 481685209688931176941 := by
  have hfermat : (2 : ZMod 481685209688931176941) ^ (481685209688931176941 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 2053) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 481685209688931176941) ^ ((481685209688931176941 - 1) / 355492486744403) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 481685209688931176941 (2 : ZMod 481685209688931176941)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 1), (2053, 1), (355492486744403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 1), (2053, 1), (355492486744403, 1)] : List FactorBlock).map factorBlockValue).prod = 481685209688931176941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64SextD_2053
      · exact prime_free64SextD_355492486744403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_4153387267 : Nat.Prime 4153387267 := by
  have hfermat : (5 : ZMod 4153387267) ^ (4153387267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 4153387267) ^ ((4153387267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 4153387267) ^ ((4153387267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 4153387267) ^ ((4153387267 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 4153387267) ^ ((4153387267 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 4153387267) ^ ((4153387267 - 1) / 215447) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4153387267 (5 : ZMod 4153387267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (7, 1), (17, 1), (215447, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (7, 1), (17, 1), (215447, 1)] : List FactorBlock).map factorBlockValue).prod = 4153387267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_free64SextD_215447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_15272295717867691 : Nat.Prime 15272295717867691 := by
  have hfermat : (2 : ZMod 15272295717867691) ^ (15272295717867691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 6451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 15272295717867691) ^ ((15272295717867691 - 1) / 4153387267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15272295717867691 (2 : ZMod 15272295717867691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (19, 1), (6451, 1), (4153387267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (19, 1), (6451, 1), (4153387267, 1)] : List FactorBlock).map factorBlockValue).prod = 15272295717867691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_free64SextD_6451
      · exact prime_free64SextD_4153387267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_1366687199200543932209 : Nat.Prime 1366687199200543932209 := by
  have hfermat : (6 : ZMod 1366687199200543932209) ^ (1366687199200543932209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1366687199200543932209) ^ ((1366687199200543932209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1366687199200543932209) ^ ((1366687199200543932209 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1366687199200543932209) ^ ((1366687199200543932209 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1366687199200543932209) ^ ((1366687199200543932209 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1366687199200543932209) ^ ((1366687199200543932209 - 1) / 15272295717867691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1366687199200543932209 (6 : ZMod 1366687199200543932209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (17, 1), (47, 1), (15272295717867691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (17, 1), (47, 1), (15272295717867691, 1)] : List FactorBlock).map factorBlockValue).prod = 1366687199200543932209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_47
      · exact prime_free64SextD_15272295717867691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_19518469961 : Nat.Prime 19518469961 := by
  have hfermat : (3 : ZMod 19518469961) ^ (19518469961 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 19518469961) ^ ((19518469961 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 19518469961) ^ ((19518469961 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 19518469961) ^ ((19518469961 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 19518469961) ^ ((19518469961 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 19518469961) ^ ((19518469961 - 1) / 561521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19518469961 (3 : ZMod 19518469961)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (79, 1), (561521, 1)] : List FactorBlock).map factorBlockValue).prod = 19518469961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_79
      · exact prime_free64SextD_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_44650621068881221949 : Nat.Prime 44650621068881221949 := by
  have hfermat : (2 : ZMod 44650621068881221949) ^ (44650621068881221949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 44650621068881221949) ^ ((44650621068881221949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 44650621068881221949) ^ ((44650621068881221949 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 44650621068881221949) ^ ((44650621068881221949 - 1) / 2161) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 44650621068881221949) ^ ((44650621068881221949 - 1) / 8537) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 44650621068881221949) ^ ((44650621068881221949 - 1) / 19518469961) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 44650621068881221949 (2 : ZMod 44650621068881221949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (2161, 1), (8537, 1), (19518469961, 1)] : List FactorBlock).map factorBlockValue).prod = 44650621068881221949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64SextD_2161
      · exact prime_free64SextD_8537
      · exact prime_free64SextD_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
  have hfermat : (3 : ZMod 1964627327030773765757) ^ (1964627327030773765757 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1964627327030773765757) ^ ((1964627327030773765757 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1964627327030773765757) ^ ((1964627327030773765757 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1964627327030773765757) ^ ((1964627327030773765757 - 1) / 44650621068881221949) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1964627327030773765757 (3 : ZMod 1964627327030773765757)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (44650621068881221949, 1)] : List FactorBlock).map factorBlockValue).prod = 1964627327030773765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64SextD_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_10103311 : Nat.Prime 10103311 := by
  have hfermat : (3 : ZMod 10103311) ^ (10103311 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 10103311) ^ ((10103311 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10103311 (3 : ZMod 10103311)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (7, 2), (29, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (7, 2), (29, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod = 10103311 - 1 by
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
      · exact prime_t64_79
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_7449654739 : Nat.Prime 7449654739 := by
  have hfermat : (2 : ZMod 7449654739) ^ (7449654739 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7449654739) ^ ((7449654739 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7449654739) ^ ((7449654739 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7449654739) ^ ((7449654739 - 1) / 32429) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7449654739) ^ ((7449654739 - 1) / 38287) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7449654739 (2 : ZMod 7449654739)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32429, 1), (38287, 1)] : List FactorBlock).map factorBlockValue).prod = 7449654739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_32429
      · exact prime_free64SextD_38287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_29798618957 : Nat.Prime 29798618957 := by
  have hfermat : (2 : ZMod 29798618957) ^ (29798618957 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 29798618957) ^ ((29798618957 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 29798618957) ^ ((29798618957 - 1) / 7449654739) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 29798618957 (2 : ZMod 29798618957)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7449654739, 1)] : List FactorBlock).map factorBlockValue).prod = 29798618957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_7449654739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64SextD_2991981134619696139127 : Nat.Prime 2991981134619696139127 := by
  have hfermat : (5 : ZMod 2991981134619696139127) ^ (2991981134619696139127 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 2991981134619696139127) ^ ((2991981134619696139127 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 2991981134619696139127) ^ ((2991981134619696139127 - 1) / 4969) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 2991981134619696139127) ^ ((2991981134619696139127 - 1) / 10103311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 2991981134619696139127) ^ ((2991981134619696139127 - 1) / 29798618957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2991981134619696139127 (5 : ZMod 2991981134619696139127)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4969, 1), (10103311, 1), (29798618957, 1)] : List FactorBlock).map factorBlockValue).prod = 2991981134619696139127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_4969
      · exact prime_free64SextD_10103311
      · exact prime_free64SextD_29798618957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_4696532563 : Nat.Prime 4696532563 := by
  have hfermat : (2 : ZMod 4696532563) ^ (4696532563 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4696532563) ^ ((4696532563 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4696532563) ^ ((4696532563 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4696532563) ^ ((4696532563 - 1) / 3823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 4696532563) ^ ((4696532563 - 1) / 204749) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4696532563 (2 : ZMod 4696532563)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3823, 1), (204749, 1)] : List FactorBlock).map factorBlockValue).prod = 4696532563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_3823
      · exact prime_free64SextD_204749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_7776862710917 : Nat.Prime 7776862710917 := by
  have hfermat : (2 : ZMod 7776862710917) ^ (7776862710917 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7776862710917) ^ ((7776862710917 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7776862710917) ^ ((7776862710917 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7776862710917) ^ ((7776862710917 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7776862710917) ^ ((7776862710917 - 1) / 1933) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 7776862710917) ^ ((7776862710917 - 1) / 3363887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7776862710917 (2 : ZMod 7776862710917)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (23, 1), (1933, 1), (3363887, 1)] : List FactorBlock).map factorBlockValue).prod = 7776862710917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_free64SextD_1933
      · exact prime_free64SextD_3363887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_73048577919604292180543 : Nat.Prime 73048577919604292180543 := by
  have hfermat : (5 : ZMod 73048577919604292180543) ^ (73048577919604292180543 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 73048577919604292180543) ^ ((73048577919604292180543 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 73048577919604292180543) ^ ((73048577919604292180543 - 1) / 4696532563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 73048577919604292180543) ^ ((73048577919604292180543 - 1) / 7776862710917) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73048577919604292180543 (5 : ZMod 73048577919604292180543)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4696532563, 1), (7776862710917, 1)] : List FactorBlock).map factorBlockValue).prod = 73048577919604292180543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_4696532563
      · exact prime_free64SextD_7776862710917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_2342693833 : Nat.Prime 2342693833 := by
  have hfermat : (11 : ZMod 2342693833) ^ (2342693833 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 2342693833) ^ ((2342693833 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 2342693833) ^ ((2342693833 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 2342693833) ^ ((2342693833 - 1) / 647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 2342693833) ^ ((2342693833 - 1) / 150869) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2342693833 (11 : ZMod 2342693833)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (647, 1), (150869, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (647, 1), (150869, 1)] : List FactorBlock).map factorBlockValue).prod = 2342693833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_647
      · exact prime_free64SextD_150869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_629210080442473 : Nat.Prime 629210080442473 := by
  have hfermat : (5 : ZMod 629210080442473) ^ (629210080442473 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 629210080442473) ^ ((629210080442473 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 629210080442473) ^ ((629210080442473 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 629210080442473) ^ ((629210080442473 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 629210080442473) ^ ((629210080442473 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 629210080442473) ^ ((629210080442473 - 1) / 2342693833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 629210080442473 (5 : ZMod 629210080442473)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (19, 2), (31, 1), (2342693833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (19, 2), (31, 1), (2342693833, 1)] : List FactorBlock).map factorBlockValue).prod = 629210080442473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_31
      · exact prime_free64SextD_2342693833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_3775260482654839 : Nat.Prime 3775260482654839 := by
  have hfermat : (3 : ZMod 3775260482654839) ^ (3775260482654839 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3775260482654839) ^ ((3775260482654839 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3775260482654839) ^ ((3775260482654839 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3775260482654839) ^ ((3775260482654839 - 1) / 629210080442473) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3775260482654839 (3 : ZMod 3775260482654839)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (629210080442473, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (629210080442473, 1)] : List FactorBlock).map factorBlockValue).prod = 3775260482654839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_629210080442473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_73681381313926227279101 : Nat.Prime 73681381313926227279101 := by
  have hfermat : (2 : ZMod 73681381313926227279101) ^ (73681381313926227279101 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 73681381313926227279101) ^ ((73681381313926227279101 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 73681381313926227279101) ^ ((73681381313926227279101 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 73681381313926227279101) ^ ((73681381313926227279101 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 73681381313926227279101) ^ ((73681381313926227279101 - 1) / 15013) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 73681381313926227279101) ^ ((73681381313926227279101 - 1) / 3775260482654839) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73681381313926227279101 (2 : ZMod 73681381313926227279101)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (13, 1), (15013, 1), (3775260482654839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (13, 1), (15013, 1), (3775260482654839, 1)] : List FactorBlock).map factorBlockValue).prod = 73681381313926227279101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64SextD_15013
      · exact prime_free64SextD_3775260482654839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_17413871 : Nat.Prime 17413871 := by
  have hfermat : (13 : ZMod 17413871) ^ (17413871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 17413871) ^ ((17413871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 17413871) ^ ((17413871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 17413871) ^ ((17413871 - 1) / 1741387) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17413871 (13 : ZMod 17413871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (1741387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (1741387, 1)] : List FactorBlock).map factorBlockValue).prod = 17413871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64SextD_1741387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_1087490951 : Nat.Prime 1087490951 := by
  have hfermat : (14 : ZMod 1087490951) ^ (1087490951 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (14 : ZMod 1087490951) ^ ((1087490951 - 1) / 4051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1087490951 (14 : ZMod 1087490951)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 1), (13, 1), (59, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 1), (13, 1), (59, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod = 1087490951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_free64SextD_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_1249870190869167187 : Nat.Prime 1249870190869167187 := by
  have hfermat : (2 : ZMod 1249870190869167187) ^ (1249870190869167187 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1249870190869167187) ^ ((1249870190869167187 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1249870190869167187) ^ ((1249870190869167187 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1249870190869167187) ^ ((1249870190869167187 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1249870190869167187) ^ ((1249870190869167187 - 1) / 17413871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1249870190869167187) ^ ((1249870190869167187 - 1) / 1087490951) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1249870190869167187 (2 : ZMod 1249870190869167187)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (17413871, 1), (1087490951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (17413871, 1), (1087490951, 1)] : List FactorBlock).map factorBlockValue).prod = 1249870190869167187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64SextD_17413871
      · exact prime_free64SextD_1087490951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_122309797138074962585447 : Nat.Prime 122309797138074962585447 := by
  have hfermat : (5 : ZMod 122309797138074962585447) ^ (122309797138074962585447 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 122309797138074962585447) ^ ((122309797138074962585447 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 122309797138074962585447) ^ ((122309797138074962585447 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 122309797138074962585447) ^ ((122309797138074962585447 - 1) / 433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 122309797138074962585447) ^ ((122309797138074962585447 - 1) / 1249870190869167187) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 122309797138074962585447 (5 : ZMod 122309797138074962585447)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (113, 1), (433, 1), (1249870190869167187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (113, 1), (433, 1), (1249870190869167187, 1)] : List FactorBlock).map factorBlockValue).prod = 122309797138074962585447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_113
      · exact prime_t64_433
      · exact prime_free64SextD_1249870190869167187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_71315977 : Nat.Prime 71315977 := by
  have hfermat : (5 : ZMod 71315977) ^ (71315977 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 71315977) ^ ((71315977 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 71315977) ^ ((71315977 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 71315977) ^ ((71315977 - 1) / 2971499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 71315977 (5 : ZMod 71315977)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2971499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2971499, 1)] : List FactorBlock).map factorBlockValue).prod = 71315977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_2971499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_14671693316257 : Nat.Prime 14671693316257 := by
  have hfermat : (5 : ZMod 14671693316257) ^ (14671693316257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 14671693316257) ^ ((14671693316257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 14671693316257) ^ ((14671693316257 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 14671693316257) ^ ((14671693316257 - 1) / 2143) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 14671693316257) ^ ((14671693316257 - 1) / 71315977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14671693316257 (5 : ZMod 14671693316257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (2143, 1), (71315977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (2143, 1), (71315977, 1)] : List FactorBlock).map factorBlockValue).prod = 14671693316257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_2143
      · exact prime_free64SextD_71315977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_1142654849326181315249383 : Nat.Prime 1142654849326181315249383 := by
  have hfermat : (6 : ZMod 1142654849326181315249383) ^ (1142654849326181315249383 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 769) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 1523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 11083) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 1142654849326181315249383) ^ ((1142654849326181315249383 - 1) / 14671693316257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1142654849326181315249383 (6 : ZMod 1142654849326181315249383)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (769, 1), (1523, 1), (11083, 1), (14671693316257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (769, 1), (1523, 1), (11083, 1), (14671693316257, 1)] : List FactorBlock).map factorBlockValue).prod = 1142654849326181315249383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64SextD_769
      · exact prime_free64SextD_1523
      · exact prime_free64SextD_11083
      · exact prime_free64SextD_14671693316257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_88217347 : Nat.Prime 88217347 := by
  have hfermat : (5 : ZMod 88217347) ^ (88217347 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 88217347) ^ ((88217347 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 88217347) ^ ((88217347 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 88217347) ^ ((88217347 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 88217347) ^ ((88217347 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 88217347) ^ ((88217347 - 1) / 4919) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 88217347 (5 : ZMod 88217347)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (61, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (61, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod = 88217347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_61
      · exact prime_free64SextD_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64SextD_23642248997 : Nat.Prime 23642248997 := by
  have hfermat : (2 : ZMod 23642248997) ^ (23642248997 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 23642248997) ^ ((23642248997 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 23642248997) ^ ((23642248997 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 23642248997) ^ ((23642248997 - 1) / 88217347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 23642248997 (2 : ZMod 23642248997)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (67, 1), (88217347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (67, 1), (88217347, 1)] : List FactorBlock).map factorBlockValue).prod = 23642248997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_free64SextD_88217347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_8227502650957 : Nat.Prime 8227502650957 := by
  have hfermat : (5 : ZMod 8227502650957) ^ (8227502650957 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 8227502650957) ^ ((8227502650957 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 8227502650957) ^ ((8227502650957 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 8227502650957) ^ ((8227502650957 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 8227502650957) ^ ((8227502650957 - 1) / 23642248997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8227502650957 (5 : ZMod 8227502650957)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (29, 1), (23642248997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (29, 1), (23642248997, 1)] : List FactorBlock).map factorBlockValue).prod = 8227502650957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_free64SextD_23642248997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64SextD_74258756761673670019 : Nat.Prime 74258756761673670019 := by
  have hfermat : (2 : ZMod 74258756761673670019) ^ (74258756761673670019 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 12641) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 74258756761673670019) ^ ((74258756761673670019 - 1) / 8227502650957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 74258756761673670019 (2 : ZMod 74258756761673670019)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (17, 1), (12641, 1), (8227502650957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (17, 1), (12641, 1), (8227502650957, 1)] : List FactorBlock).map factorBlockValue).prod = 74258756761673670019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_free64SextD_12641
      · exact prime_free64SextD_8227502650957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64SextD_1633692648756820740419 : Nat.Prime 1633692648756820740419 := by
  have hfermat : (2 : ZMod 1633692648756820740419) ^ (1633692648756820740419 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1633692648756820740419) ^ ((1633692648756820740419 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1633692648756820740419) ^ ((1633692648756820740419 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1633692648756820740419) ^ ((1633692648756820740419 - 1) / 74258756761673670019) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1633692648756820740419 (2 : ZMod 1633692648756820740419)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (74258756761673670019, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (74258756761673670019, 1)] : List FactorBlock).map factorBlockValue).prod = 1633692648756820740419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64SextD_74258756761673670019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_1767655445954880041133359 : Nat.Prime 1767655445954880041133359 := by
  have hfermat : (7 : ZMod 1767655445954880041133359) ^ (1767655445954880041133359 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 1767655445954880041133359) ^ ((1767655445954880041133359 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 1767655445954880041133359) ^ ((1767655445954880041133359 - 1) / 541) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 1767655445954880041133359) ^ ((1767655445954880041133359 - 1) / 1633692648756820740419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1767655445954880041133359 (7 : ZMod 1767655445954880041133359)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (541, 1), (1633692648756820740419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (541, 1), (1633692648756820740419, 1)] : List FactorBlock).map factorBlockValue).prod = 1767655445954880041133359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64SextD_541
      · exact prime_free64SextD_1633692648756820740419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64SextD_74669487417020353737559681 : Nat.Prime 74669487417020353737559681 := by
  have hfermat : (67 : ZMod 74669487417020353737559681) ^ (74669487417020353737559681 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (67 : ZMod 74669487417020353737559681) ^ ((74669487417020353737559681 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 74669487417020353737559681 (67 : ZMod 74669487417020353737559681)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 74669487417020353737559681 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_77104362006705800055088801 : Nat.Prime 77104362006705800055088801 := by
  have hfermat : (73 : ZMod 77104362006705800055088801) ^ (77104362006705800055088801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (73 : ZMod 77104362006705800055088801) ^ ((77104362006705800055088801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 77104362006705800055088801 (73 : ZMod 77104362006705800055088801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 77104362006705800055088801 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_88670016307711670063352121 : Nat.Prime 88670016307711670063352121 := by
  have hfermat : (83 : ZMod 88670016307711670063352121) ^ (88670016307711670063352121 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (83 : ZMod 88670016307711670063352121) ^ ((88670016307711670063352121 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 88670016307711670063352121 (83 : ZMod 88670016307711670063352121)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 88670016307711670063352121 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17

private theorem prime_free64SextD_126671451868159528661931601 : Nat.Prime 126671451868159528661931601 := by
  have hfermat : (89 : ZMod 126671451868159528661931601) ^ (126671451868159528661931601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (89 : ZMod 126671451868159528661931601) ^ ((126671451868159528661931601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 126671451868159528661931601 (89 : ZMod 126671451868159528661931601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 4), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 126671451868159528661931601 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16
    · exact hfactor_17

private theorem prime_free64SextD_141872026092338672101363393 : Nat.Prime 141872026092338672101363393 := by
  have hfermat : (5 : ZMod 141872026092338672101363393) ^ (141872026092338672101363393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (5 : ZMod 141872026092338672101363393) ^ ((141872026092338672101363393 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 141872026092338672101363393 (5 : ZMod 141872026092338672101363393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 141872026092338672101363393 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_208635332488733341325534401 : Nat.Prime 208635332488733341325534401 := by
  have hfermat : (79 : ZMod 208635332488733341325534401) ^ (208635332488733341325534401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (79 : ZMod 208635332488733341325534401) ^ ((208635332488733341325534401 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 208635332488733341325534401 (79 : ZMod 208635332488733341325534401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 208635332488733341325534401 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
  have hfermat : (39 : ZMod 272830819408343600194929601) ^ (272830819408343600194929601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (39 : ZMod 272830819408343600194929601) ^ ((272830819408343600194929601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 272830819408343600194929601 (39 : ZMod 272830819408343600194929601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 272830819408343600194929601 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  have hfermat : (13 : ZMod 545661638816687200389859201) ^ (545661638816687200389859201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (13 : ZMod 545661638816687200389859201) ^ ((545661638816687200389859201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 545661638816687200389859201 - 1 by
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
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7
    · exact hfactor_8
    · exact hfactor_9
    · exact hfactor_10
    · exact hfactor_11
    · exact hfactor_12
    · exact hfactor_13
    · exact hfactor_14
    · exact hfactor_15
    · exact hfactor_16

private theorem prime_free64SextD_7093601304616933605068169673 : Nat.Prime 7093601304616933605068169673 := by
  have hfermat : (5 : ZMod 7093601304616933605068169673) ^ (7093601304616933605068169673 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 7093601304616933605068169673) ^ ((7093601304616933605068169673 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 7093601304616933605068169673) ^ ((7093601304616933605068169673 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 7093601304616933605068169673) ^ ((7093601304616933605068169673 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 7093601304616933605068169673) ^ ((7093601304616933605068169673 - 1) / 1115447) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 7093601304616933605068169673) ^ ((7093601304616933605068169673 - 1) / 284004322561366753) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7093601304616933605068169673 (5 : ZMod 7093601304616933605068169673)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod = 7093601304616933605068169673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_311
      · exact prime_t64_1115447
      · exact prime_lucas_284004322561366753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem phi_free64SextD_7093601304616933605068169600 :
    Nat.totient 7093601304616933605068169600 = 933428210756163836313600000 := by
  rw [← show
    ((([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169600 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169601 :
    Nat.totient 7093601304616933605068169601 = 7093540101479519638185792480 := by
  rw [← show
    ((([(115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169601 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_115903, prime_free64SextD_32244294937, prime_free64SextD_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169602 :
    Nat.totient 7093601304616933605068169602 = 3546800652191906989338726100 := by
  rw [← show
    ((([(2, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169602 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64SextD_30429025931, prime_free64SextD_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169603 :
    Nat.totient 7093601304616933605068169603 = 4729045037719437242015215104 := by
  rw [← show
    ((([(3, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169603 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169604 :
    Nat.totient 7093601304616933605068169604 = 3546331617394483884577175040 := by
  rw [← show
    ((([(2, 2), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169604 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64SextD_8233, prime_free64SextD_93811, prime_free64SextD_8274073, prime_free64SextD_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169605 :
    Nat.totient 7093601304616933605068169605 = 5669430579905049339327700992 := by
  rw [← show
    ((([(5, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169605 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64SextD_1049, prime_free64SextD_139537, prime_free64SextD_175593973, prime_free64SextD_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169606 :
    Nat.totient 7093601304616933605068169606 = 2341109655706591279001952384 := by
  rw [← show
    ((([(2, 1), (3, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169606 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169607 :
    Nat.totient 7093601304616933605068169607 = 6061010105625022236121773120 := by
  rw [← show
    ((([(7, 1), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169607 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64SextD_331, prime_free64SextD_7129, prime_free64SextD_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169608 :
    Nat.totient 7093601304616933605068169608 = 3540123320806535402535321600 := by
  rw [← show
    ((([(2, 3), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169608 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64SextD_769, prime_free64SextD_2143, prime_free64SextD_8597, prime_free64SextD_9792301, prime_free64SextD_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169609 :
    Nat.totient 7093601304616933605068169609 = 4714649187782696736432768000 := by
  rw [← show
    ((([(3, 2), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169609 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169610 :
    Nat.totient 7093601304616933605068169610 = 2823516964197063832352578560 := by
  rw [← show
    ((([(2, 1), (5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169610 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64SextD_281, prime_free64SextD_739, prime_free64SextD_3540386347, prime_free64SextD_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169611 :
    Nat.totient 7093601304616933605068169611 = 6448629667797616587757691040 := by
  rw [← show
    ((([(11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169611 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_free64SextD_97327, prime_free64SextD_208223, prime_free64SextD_4129087, prime_free64SextD_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169612 :
    Nat.totient 7093601304616933605068169612 = 2364533766271648981528824400 := by
  rw [← show
    ((([(2, 2), (3, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169612 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169613 :
    Nat.totient 7093601304616933605068169613 = 6547939665800246404678310400 := by
  rw [← show
    ((([(13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169613 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_free64SextD_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169614 :
    Nat.totient 7093601304616933605068169614 = 3035933043531011885696786208 := by
  rw [← show
    ((([(2, 1), (7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169614 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64SextD_727, prime_free64SextD_40346827, prime_free64SextD_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169615 :
    Nat.totient 7093601304616933605068169615 = 3766550734750699236795076224 := by
  rw [← show
    ((([(3, 1), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169615 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169616 :
    Nat.totient 7093601304616933605068169616 = 3537200714323009588295639040 := by
  rw [← show
    ((([(2, 4), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169616 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64SextD_373, prime_free64SextD_55249, prime_free64SextD_157429, prime_free64SextD_773027, prime_free64SextD_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169617 :
    Nat.totient 7093601304616933605068169617 = 6597102979194737368650812928 := by
  rw [← show
    ((([(17, 1), (89, 1), (1567, 1), (2991981134619696139127, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169617 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_89, prime_free64SextD_1567, prime_free64SextD_2991981134619696139127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169618 :
    Nat.totient 7093601304616933605068169618 = 2364533768205644535022723200 := by
  rw [← show
    ((([(2, 1), (3, 2), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169618 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169619 :
    Nat.totient 7093601304616933605068169619 = 6720251389869997214810758656 := by
  rw [← show
    ((([(19, 1), (2712337, 1), (137647879701195599473, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169619 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_free64SextD_2712337, prime_free64SextD_137647879701195599473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169620 :
    Nat.totient 7093601304616933605068169620 = 2837424804828157195835697536 := by
  rw [← show
    ((([(2, 2), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169620 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64SextD_180533, prime_free64SextD_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169621 :
    Nat.totient 7093601304616933605068169621 = 4053444895365943559296683504 := by
  rw [← show
    ((([(3, 1), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169621 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169622 :
    Nat.totient 7093601304616933605068169622 = 3223668872151569955168257280 := by
  rw [← show
    ((([(2, 1), (11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169622 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64SextD_4637, prime_free64SextD_2076644077, prime_free64SextD_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169623 :
    Nat.totient 7093601304616933605068169623 = 6777865580963869085497047552 := by
  rw [← show
    ((([(23, 2), (953, 1), (34157, 1), (485319319, 1), (848810813, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169623 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_free64SextD_953, prime_free64SextD_34157, prime_free64SextD_485319319, prime_free64SextD_848810813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169624 :
    Nat.totient 7093601304616933605068169624 = 2364533655236198298650382336 := by
  rw [← show
    ((([(2, 3), (3, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169624 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169625 :
    Nat.totient 7093601304616933605068169625 = 5603035664005522105654512000 := by
  rw [← show
    ((([(5, 3), (79, 1), (489673, 1), (1466977702710658571, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169625 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_79, prime_free64SextD_489673, prime_free64SextD_1466977702710658571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169626 :
    Nat.totient 7093601304616933605068169626 = 3273969832900123202339155200 := by
  rw [← show
    ((([(2, 1), (13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169626 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_free64SextD_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169627 :
    Nat.totient 7093601304616933605068169627 = 4644614488941132679148313600 := by
  rw [← show
    ((([(3, 3), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169627 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_67, prime_t64_491, prime_t64_1061, prime_t64_9492089, prime_lucas_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169628 :
    Nat.totient 7093601304616933605068169628 = 3040099278051909269450822400 := by
  rw [← show
    ((([(2, 2), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169628 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64SextD_339389, prime_free64SextD_545911, prime_free64SextD_2940799, prime_free64SextD_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169629 :
    Nat.totient 7093601304616933605068169629 = 6796711963245918864328913280 := by
  rw [← show
    ((([(29, 1), (131, 1), (59553859433, 1), (31353611321587, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169629 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_free64SextD_131, prime_free64SextD_59553859433, prime_free64SextD_31353611321587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169630 :
    Nat.totient 7093601304616933605068169630 = 1891627011543136663647837216 := by
  rw [← show
    ((([(2, 1), (3, 1), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169630 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169631 :
    Nat.totient 7093601304616933605068169631 = 6804025230765774565165248000 := by
  rw [← show
    ((([(31, 1), (113, 1), (172263064301, 1), (11755320372277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169631 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_t64_113, prime_free64SextD_172263064301, prime_free64SextD_11755320372277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169632 :
    Nat.totient 7093601304616933605068169632 = 3515752135273223057525913600 := by
  rw [← show
    ((([(2, 5), (197, 1), (271, 1), (152441, 1), (27238268144131903, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169632 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_197, prime_free64SextD_271, prime_free64SextD_152441, prime_free64SextD_27238268144131903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169633 :
    Nat.totient 7093601304616933605068169633 = 4299152305828444609132224000 := by
  rw [← show
    ((([(3, 1), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169633 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_lucas_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169634 :
    Nat.totient 7093601304616933605068169634 = 3338165319819733461208550400 := by
  rw [← show
    ((([(2, 1), (17, 1), (208635332488733341325534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169634 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64SextD_208635332488733341325534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169635 :
    Nat.totient 7093601304616933605068169635 = 4864183751546818553169075168 := by
  rw [← show
    ((([(5, 1), (7, 1), (25532870323, 1), (7937780610842107, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169635 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_free64SextD_25532870323, prime_free64SextD_7937780610842107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169636 :
    Nat.totient 7093601304616933605068169636 = 2358700242841490567164661376 := by
  rw [← show
    ((([(2, 2), (3, 2), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169636 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169637 :
    Nat.totient 7093601304616933605068169637 = 6901348974561722563364579328 := by
  rw [← show
    ((([(37, 1), (14939, 1), (97303, 1), (15555937, 1), (8478540869, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169637 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_free64SextD_14939, prime_free64SextD_97303, prime_free64SextD_15555937, prime_free64SextD_8478540869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169638 :
    Nat.totient 7093601304616933605068169638 = 3360126923328651614184211272 := by
  rw [← show
    ((([(2, 1), (19, 1), (321935599, 1), (579848016567285199, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169638 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_free64SextD_321935599, prime_free64SextD_579848016567285199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169639 :
    Nat.totient 7093601304616933605068169639 = 4365293110532487154920609888 := by
  rw [← show
    ((([(3, 1), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169639 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_lucas_4887540332063, prime_lucas_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169640 :
    Nat.totient 7093601304616933605068169640 = 2819022944168352897362619648 := by
  rw [← show
    ((([(2, 3), (5, 1), (157, 1), (8179, 1), (138104211745804923847, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169640 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_157, prime_free64SextD_8179, prime_free64SextD_138104211745804923847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169641 :
    Nat.totient 7093601304616933605068169641 = 6920586604285994144422352160 := by
  rw [← show
    ((([(41, 1), (201386659, 1), (859116819482400139, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169641 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_free64SextD_201386659, prime_free64SextD_859116819482400139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169642 :
    Nat.totient 7093601304616933605068169642 = 2022346823602002270213839040 := by
  rw [← show
    ((([(2, 1), (3, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169642 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169643 :
    Nat.totient 7093601304616933605068169643 = 6927169760638880408570154240 := by
  rw [← show
    ((([(43, 1), (4733, 1), (40086377, 1), (869490835208461, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169643 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_free64SextD_4733, prime_free64SextD_40086377, prime_free64SextD_869490835208461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169644 :
    Nat.totient 7093601304616933605068169644 = 3222903257812941371005513040 := by
  rw [← show
    ((([(2, 2), (11, 1), (2207, 1), (73048577919604292180543, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169644 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64SextD_2207, prime_free64SextD_73048577919604292180543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169645 :
    Nat.totient 7093601304616933605068169645 = 3783247959208451340716605536 := by
  rw [← show
    ((([(3, 2), (5, 1), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169645 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_623279, prime_lucas_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169646 :
    Nat.totient 7093601304616933605068169646 = 3392591924831463654444958264 := by
  rw [← show
    ((([(2, 1), (23, 1), (979501163, 1), (157435978474087427, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169646 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_free64SextD_979501163, prime_free64SextD_157435978474087427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169647 :
    Nat.totient 7093601304616933605068169647 = 6911250351864593344767682560 := by
  rw [← show
    ((([(47, 1), (223, 1), (23879, 1), (9096713, 1), (3115755898081, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169647 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_223, prime_free64SextD_23879, prime_free64SextD_9096713, prime_free64SextD_3115755898081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169648 :
    Nat.totient 7093601304616933605068169648 = 2352154001917303943676602880 := by
  rw [← show
    ((([(2, 4), (3, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169648 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169649 :
    Nat.totient 7093601304616933605068169649 = 6058623048570019788134400000 := by
  rw [← show
    ((([(7, 2), (457, 1), (743, 1), (74071, 1), (110681, 1), (52004916001, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169649 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64SextD_457, prime_free64SextD_743, prime_free64SextD_74071, prime_free64SextD_110681, prime_free64SextD_52004916001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169650 :
    Nat.totient 7093601304616933605068169650 = 2837440521846773442027267840 := by
  rw [← show
    ((([(2, 1), (5, 2), (141872026092338672101363393, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169650 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64SextD_141872026092338672101363393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169651 :
    Nat.totient 7093601304616933605068169651 = 4427301007024085332608860160 := by
  rw [← show
    ((([(3, 1), (17, 1), (229, 1), (1669, 1), (2963, 1), (108608761, 1), (1130858507, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169651 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_229, prime_t64_1669, prime_t64_2963, prime_lucas_108608761, prime_lucas_1130858507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169652 :
    Nat.totient 7093601304616933605068169652 = 3264695130493371152484910080 := by
  rw [← show
    ((([(2, 2), (13, 1), (353, 1), (9879116647, 1), (39117456919511, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169652 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_free64SextD_353, prime_free64SextD_9879116647, prime_free64SextD_39117456919511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169653 :
    Nat.totient 7093601304616933605068169653 = 6906232983326084711191437120 := by
  rw [← show
    ((([(53, 1), (139, 1), (1999, 1), (481685209688931176941, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169653 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_t64_139, prime_free64SextD_1999, prime_free64SextD_481685209688931176941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169654 :
    Nat.totient 7093601304616933605068169654 = 2364533768205644535022723200 := by
  rw [← show
    ((([(2, 1), (3, 3), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169654 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169655 :
    Nat.totient 7093601304616933605068169655 = 5156072846366579686385141760 := by
  rw [← show
    ((([(5, 1), (11, 1), (1777, 1), (1260383, 1), (1959283, 1), (29391175157, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169655 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_free64SextD_1777, prime_free64SextD_1260383, prime_free64SextD_1959283, prime_free64SextD_29391175157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169656 :
    Nat.totient 7093601304616933605068169656 = 3040114844835828687886358400 := by
  rw [← show
    ((([(2, 3), (7, 1), (126671451868159528661931601, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169656 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64SextD_126671451868159528661931601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169657 :
    Nat.totient 7093601304616933605068169657 = 4431440825772889578928128000 := by
  rw [← show
    ((([(3, 1), (19, 1), (149, 1), (349, 1), (1213, 1), (2897, 1), (6151, 1), (110719776691, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169657 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_t64_149, prime_t64_349, prime_t64_1213, prime_t64_2897, prime_t64_6151, prime_lucas_110719776691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169658 :
    Nat.totient 7093601304616933605068169658 = 3388946914113604777817533440 := by
  rw [← show
    ((([(2, 1), (29, 1), (109, 1), (821, 1), (1366687199200543932209, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169658 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_t64_109, prime_free64SextD_821, prime_free64SextD_1366687199200543932209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169659 :
    Nat.totient 7093601304616933605068169659 = 6966276805796197569016662376 := by
  rw [← show
    ((([(59, 1), (983, 1), (122309797138074962585447, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169659 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_free64SextD_983, prime_free64SextD_122309797138074962585447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169660 :
    Nat.totient 7093601304616933605068169660 = 1872898034222292701008096000 := by
  rw [← show
    ((([(2, 2), (3, 1), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169660 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169661 :
    Nat.totient 7093601304616933605068169661 = 6909992583474177562467674880 := by
  rw [← show
    ((([(61, 1), (107, 1), (6133, 1), (7019, 1), (25246719536515909, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169661 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_t64_107, prime_free64SextD_6133, prime_free64SextD_7019, prime_free64SextD_25246719536515909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169662 :
    Nat.totient 7093601304616933605068169662 = 3360802780989327324598272000 := by
  rw [← show
    ((([(2, 1), (31, 1), (73, 1), (193, 1), (811, 1), (1171, 1), (8551005138652489, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169662 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_t64_73, prime_t64_193, prime_free64SextD_811, prime_free64SextD_1171, prime_free64SextD_8551005138652489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169663 :
    Nat.totient 7093601304616933605068169663 = 4052247622759736705821999104 := by
  rw [← show
    ((([(3, 2), (7, 1), (4787, 1), (10337, 1), (269456833, 1), (8444599963, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169663 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_4787, prime_t64_10337, prime_lucas_269456833, prime_lucas_8444599963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169664 :
    Nat.totient 7093601304616933605068169664 = 3510235697130029000446101504 := by
  rw [← show
    ((([(2, 6), (97, 1), (1142654849326181315249383, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169664 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_97, prime_free64SextD_1142654849326181315249383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169665 :
    Nat.totient 7093601304616933605068169665 = 5238324128372275583930327040 := by
  rw [← show
    ((([(5, 1), (13, 1), (192613, 1), (12838541, 1), (44131851767777, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169665 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_free64SextD_192613, prime_free64SextD_12838541, prime_free64SextD_44131851767777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169666 :
    Nat.totient 7093601304616933605068169666 = 2149576152914222304566112000 := by
  rw [← show
    ((([(2, 1), (3, 1), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169666 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169667 :
    Nat.totient 7093601304616933605068169667 = 7091833649170978725027032296 := by
  rw [← show
    ((([(4013, 1), (1767655445954880041133359, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169667 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_4013, prime_free64SextD_1767655445954880041133359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169668 :
    Nat.totient 7093601304616933605068169668 = 3338163805601872952797188096 := by
  rw [← show
    ((([(2, 2), (17, 1), (2217799, 1), (370033847, 1), (127114246817, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169668 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64SextD_2217799, prime_free64SextD_370033847, prime_free64SextD_127114246817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169669 :
    Nat.totient 7093601304616933605068169669 = 4521097907678769636381566976 := by
  rw [← show
    ((([(3, 1), (23, 1), (2417, 1), (9343, 1), (1789993, 1), (2543333740247, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169669 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_t64_2417, prime_t64_9343, prime_t64_1789993, prime_lucas_2543333740247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169670 :
    Nat.totient 7093601304616933605068169670 = 2396459925868615180995133440 := by
  rw [← show
    ((([(2, 1), (5, 1), (7, 1), (71, 1), (2549, 1), (6113, 1), (54049, 1), (1694722097147, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169670 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_71, prime_free64SextD_2549, prime_free64SextD_6113, prime_free64SextD_54049, prime_free64SextD_1694722097147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169671 :
    Nat.totient 7093601304616933605068169671 = 7091678201391520981950303360 := by
  rw [← show
    ((([(4957, 1), (22147, 1), (41269, 1), (1565701635647021, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169671 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_4957, prime_free64SextD_22147, prime_free64SextD_41269, prime_free64SextD_1565701635647021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169672 :
    Nat.totient 7093601304616933605068169672 = 2356928652743370057502356480 := by
  rw [← show
    ((([(2, 3), (3, 2), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169672 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_311, prime_t64_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169673 :
    Nat.totient 7093601304616933605068169673 = 7093601304616933605068169672 := by
  rw [← show
    ((([(7093601304616933605068169673, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169673 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_7093601304616933605068169673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169674 :
    Nat.totient 7093601304616933605068169674 = 3448288645491747436661880000 := by
  rw [← show
    ((([(2, 1), (37, 1), (1301, 1), (73681381313926227279101, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169674 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_free64SextD_1301, prime_free64SextD_73681381313926227279101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169675 :
    Nat.totient 7093601304616933605068169675 = 3779436340660605043619376000 := by
  rw [← show
    ((([(3, 1), (5, 2), (991, 1), (49777621, 1), (1917333766315939, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169675 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_991, prime_lucas_49777621, prime_lucas_1917333766315939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169676 :
    Nat.totient 7093601304616933605068169676 = 3311686365149855913006608640 := by
  rw [← show
    ((([(2, 2), (19, 1), (83, 1), (733, 1), (967, 1), (171370811, 1), (9257799907, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169676 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_83, prime_free64SextD_733, prime_free64SextD_967, prime_free64SextD_171370811, prime_free64SextD_9257799907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169677 :
    Nat.totient 7093601304616933605068169677 = 5527481535790653027778168320 := by
  rw [← show
    ((([(7, 1), (11, 2), (20138250467, 1), (415873863425473, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169677 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_free64SextD_20138250467, prime_free64SextD_415873863425473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169678 :
    Nat.totient 7093601304616933605068169678 = 2182644900860521172980664448 := by
  rw [← show
    ((([(2, 1), (3, 1), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169678 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_t64_1319293, prime_lucas_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169679 :
    Nat.totient 7093601304616933605068169679 = 7044218498671844488110040320 := by
  rw [← show
    ((([(167, 1), (1021, 1), (128531593, 1), (323679110497829, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169679 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_167, prime_free64SextD_1021, prime_free64SextD_128531593, prime_free64SextD_323679110497829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169680 :
    Nat.totient 7093601304616933605068169680 = 2837440521846773442027267840 := by
  rw [← show
    ((([(2, 4), (5, 1), (88670016307711670063352121, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169680 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64SextD_88670016307711670063352121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169681 :
    Nat.totient 7093601304616933605068169681 = 4727375744919894354790494720 := by
  rw [← show
    ((([(3, 5), (3511, 1), (13709, 1), (606490351024352033, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169681 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_3511, prime_t64_13709, prime_lucas_606490351024352033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169682 :
    Nat.totient 7093601304616933605068169682 = 3460292839308592660388318080 := by
  rw [← show
    ((([(2, 1), (41, 1), (7208693, 1), (12000418520130256157, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169682 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_free64SextD_7208693, prime_free64SextD_12000418520130256157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169683 :
    Nat.totient 7093601304616933605068169683 = 7093600454471989578741213160 := by
  rw [← show
    ((([(8529779, 1), (383150387, 1), (2170499687771, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169683 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_8529779, prime_free64SextD_383150387, prime_free64SextD_2170499687771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169684 :
    Nat.totient 7093601304616933605068169684 = 2019318916409645727744000000 := by
  rw [← show
    ((([(2, 2), (3, 1), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169684 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_433, prime_t64_751, prime_t64_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169685 :
    Nat.totient 7093601304616933605068169685 = 5339422622759946833105510400 := by
  rw [← show
    ((([(5, 1), (17, 1), (3253, 1), (94382443801, 1), (271814467237, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169685 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_free64SextD_3253, prime_free64SextD_94382443801, prime_free64SextD_271814467237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169686 :
    Nat.totient 7093601304616933605068169686 = 3464121860416977850674017280 := by
  rw [← show
    ((([(2, 1), (43, 1), (17761, 1), (891929189, 1), (5206795646669, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169686 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_free64SextD_17761, prime_free64SextD_891929189, prime_free64SextD_5206795646669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169687 :
    Nat.totient 7093601304616933605068169687 = 4560814226177594269220044800 := by
  rw [← show
    ((([(3, 1), (29, 1), (1229, 1), (3121, 1), (911749, 1), (23314525201361, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169687 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_1229, prime_t64_3121, prime_t64_911749, prime_lucas_23314525201361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169688 :
    Nat.totient 7093601304616933605068169688 = 3224364229368431291246400000 := by
  rw [← show
    ((([(2, 3), (11, 1), (1128574980601, 1), (71425565088601, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169688 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64SextD_1128574980601, prime_free64SextD_71425565088601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169689 :
    Nat.totient 7093601304616933605068169689 = 7093382561561732960955974400 := by
  rw [← show
    ((([(32429, 1), (13359593581, 1), (16373441488561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169689 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_32429, prime_free64SextD_13359593581, prime_free64SextD_16373441488561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169690 :
    Nat.totient 7093601304616933605068169690 = 1891626654257559177342033888 := by
  rw [← show
    ((([(2, 1), (3, 2), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169690 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_5250043, prime_lucas_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169691 :
    Nat.totient 7093601304616933605068169691 = 5581492928713964309359104000 := by
  rw [← show
    ((([(7, 1), (13, 1), (181, 1), (303713, 1), (661973267, 1), (2142115951, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169691 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_free64SextD_181, prime_free64SextD_303713, prime_free64SextD_661973267, prime_free64SextD_2142115951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169692 :
    Nat.totient 7093601304616933605068169692 = 3392591928295055202423907200 := by
  rw [← show
    ((([(2, 2), (23, 1), (77104362006705800055088801, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169692 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_free64SextD_77104362006705800055088801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169693 :
    Nat.totient 7093601304616933605068169693 = 4576496758337154827847352320 := by
  rw [← show
    ((([(3, 1), (31, 1), (241513, 1), (3623449, 1), (87160790647873, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169693 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_t64_241513, prime_t64_3623449, prime_lucas_87160790647873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169694 :
    Nat.totient 7093601304616933605068169694 = 3419525797039499211249150240 := by
  rw [← show
    ((([(2, 1), (47, 1), (67, 1), (236499493, 1), (4762488116064271, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169694 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_t64_67, prime_free64SextD_236499493, prime_free64SextD_4762488116064271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169695 :
    Nat.totient 7093601304616933605068169695 = 5376203094025465469104296960 := by
  rw [← show
    ((([(5, 1), (19, 1), (74669487417020353737559681, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169695 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_free64SextD_74669487417020353737559681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169696 :
    Nat.totient 7093601304616933605068169696 = 2364533768193799604402617344 := by
  rw [← show
    ((([(2, 5), (3, 1), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169696 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64SextD_7093601304616933605068169697 :
    Nat.totient 7093601304616933605068169697 = 7093532490984460978224461712 := by
  rw [← show
    ((([(103087, 1), (3857112107, 1), (17840236707533, 1)] : List FactorBlock).map factorBlockValue).prod) = 7093601304616933605068169697 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64SextD_103087, prime_free64SextD_3857112107, prime_free64SextD_17840236707533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- A free-position kill one below six times `periodLcm 64`. -/
theorem freeKill_64SextD :
    certifiedKill 1 7093601304616933605068169599 97 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free64SextD_7093601304616933605068169600,
    phi_free64SextD_7093601304616933605068169601,
    phi_free64SextD_7093601304616933605068169602,
    phi_free64SextD_7093601304616933605068169603,
    phi_free64SextD_7093601304616933605068169604,
    phi_free64SextD_7093601304616933605068169605,
    phi_free64SextD_7093601304616933605068169606,
    phi_free64SextD_7093601304616933605068169607,
    phi_free64SextD_7093601304616933605068169608,
    phi_free64SextD_7093601304616933605068169609,
    phi_free64SextD_7093601304616933605068169610,
    phi_free64SextD_7093601304616933605068169611,
    phi_free64SextD_7093601304616933605068169612,
    phi_free64SextD_7093601304616933605068169613,
    phi_free64SextD_7093601304616933605068169614,
    phi_free64SextD_7093601304616933605068169615,
    phi_free64SextD_7093601304616933605068169616,
    phi_free64SextD_7093601304616933605068169617,
    phi_free64SextD_7093601304616933605068169618,
    phi_free64SextD_7093601304616933605068169619,
    phi_free64SextD_7093601304616933605068169620,
    phi_free64SextD_7093601304616933605068169621,
    phi_free64SextD_7093601304616933605068169622,
    phi_free64SextD_7093601304616933605068169623,
    phi_free64SextD_7093601304616933605068169624,
    phi_free64SextD_7093601304616933605068169625,
    phi_free64SextD_7093601304616933605068169626,
    phi_free64SextD_7093601304616933605068169627,
    phi_free64SextD_7093601304616933605068169628,
    phi_free64SextD_7093601304616933605068169629,
    phi_free64SextD_7093601304616933605068169630,
    phi_free64SextD_7093601304616933605068169631,
    phi_free64SextD_7093601304616933605068169632,
    phi_free64SextD_7093601304616933605068169633,
    phi_free64SextD_7093601304616933605068169634,
    phi_free64SextD_7093601304616933605068169635,
    phi_free64SextD_7093601304616933605068169636,
    phi_free64SextD_7093601304616933605068169637,
    phi_free64SextD_7093601304616933605068169638,
    phi_free64SextD_7093601304616933605068169639,
    phi_free64SextD_7093601304616933605068169640,
    phi_free64SextD_7093601304616933605068169641,
    phi_free64SextD_7093601304616933605068169642,
    phi_free64SextD_7093601304616933605068169643,
    phi_free64SextD_7093601304616933605068169644,
    phi_free64SextD_7093601304616933605068169645,
    phi_free64SextD_7093601304616933605068169646,
    phi_free64SextD_7093601304616933605068169647,
    phi_free64SextD_7093601304616933605068169648,
    phi_free64SextD_7093601304616933605068169649,
    phi_free64SextD_7093601304616933605068169650,
    phi_free64SextD_7093601304616933605068169651,
    phi_free64SextD_7093601304616933605068169652,
    phi_free64SextD_7093601304616933605068169653,
    phi_free64SextD_7093601304616933605068169654,
    phi_free64SextD_7093601304616933605068169655,
    phi_free64SextD_7093601304616933605068169656,
    phi_free64SextD_7093601304616933605068169657,
    phi_free64SextD_7093601304616933605068169658,
    phi_free64SextD_7093601304616933605068169659,
    phi_free64SextD_7093601304616933605068169660,
    phi_free64SextD_7093601304616933605068169661,
    phi_free64SextD_7093601304616933605068169662,
    phi_free64SextD_7093601304616933605068169663,
    phi_free64SextD_7093601304616933605068169664,
    phi_free64SextD_7093601304616933605068169665,
    phi_free64SextD_7093601304616933605068169666,
    phi_free64SextD_7093601304616933605068169667,
    phi_free64SextD_7093601304616933605068169668,
    phi_free64SextD_7093601304616933605068169669,
    phi_free64SextD_7093601304616933605068169670,
    phi_free64SextD_7093601304616933605068169671,
    phi_free64SextD_7093601304616933605068169672,
    phi_free64SextD_7093601304616933605068169673,
    phi_free64SextD_7093601304616933605068169674,
    phi_free64SextD_7093601304616933605068169675,
    phi_free64SextD_7093601304616933605068169676,
    phi_free64SextD_7093601304616933605068169677,
    phi_free64SextD_7093601304616933605068169678,
    phi_free64SextD_7093601304616933605068169679,
    phi_free64SextD_7093601304616933605068169680,
    phi_free64SextD_7093601304616933605068169681,
    phi_free64SextD_7093601304616933605068169682,
    phi_free64SextD_7093601304616933605068169683,
    phi_free64SextD_7093601304616933605068169684,
    phi_free64SextD_7093601304616933605068169685,
    phi_free64SextD_7093601304616933605068169686,
    phi_free64SextD_7093601304616933605068169687,
    phi_free64SextD_7093601304616933605068169688,
    phi_free64SextD_7093601304616933605068169689,
    phi_free64SextD_7093601304616933605068169690,
    phi_free64SextD_7093601304616933605068169691,
    phi_free64SextD_7093601304616933605068169692,
    phi_free64SextD_7093601304616933605068169693,
    phi_free64SextD_7093601304616933605068169694,
    phi_free64SextD_7093601304616933605068169695,
    phi_free64SextD_7093601304616933605068169696,
    phi_free64SextD_7093601304616933605068169697]

end TotientTailPeriodKiller
end Erdos249257
