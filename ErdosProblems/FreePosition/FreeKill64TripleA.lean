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
  prime_t64_269
  prime_t64_311
  prime_t64_349
  prime_t64_409
  prime_t64_431
  prime_t64_433
  prime_t64_461
  prime_t64_467
  prime_t64_499
  prime_t64_647
  prime_t64_661
  prime_t64_751
  prime_t64_761
  prime_t64_787
  prime_t64_1051
  prime_t64_1153
  prime_t64_1423
  prime_t64_1579
  prime_t64_2897
  prime_t64_4001
  prime_t64_4271
  prime_t64_5009
  prime_t64_7901
  prime_t64_39551
  prime_t64_45127
  prime_t64_65353
  prime_t64_149059
  prime_t64_940369
  prime_t64_1115447
  prime_t64_1319293
  prime_t64_2106407
  prime_t64_3748763
  prime_t64_4597727
  prime_t64_5160187
  prime_t64_5250043
  prime_t64_6947861
  prime_t64_8295863
  prime_t64_12040159
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private theorem prime_free64TripleA_127 : Nat.Prime 127 := by norm_num
private theorem prime_free64TripleA_131 : Nat.Prime 131 := by norm_num
private theorem prime_free64TripleA_151 : Nat.Prime 151 := by norm_num
private theorem prime_free64TripleA_173 : Nat.Prime 173 := by norm_num
private theorem prime_free64TripleA_181 : Nat.Prime 181 := by norm_num
private theorem prime_free64TripleA_199 : Nat.Prime 199 := by norm_num
private theorem prime_free64TripleA_211 : Nat.Prime 211 := by norm_num
private theorem prime_free64TripleA_241 : Nat.Prime 241 := by norm_num
private theorem prime_free64TripleA_257 : Nat.Prime 257 := by norm_num
private theorem prime_free64TripleA_271 : Nat.Prime 271 := by norm_num
private theorem prime_free64TripleA_281 : Nat.Prime 281 := by norm_num
private theorem prime_free64TripleA_313 : Nat.Prime 313 := by norm_num
private theorem prime_free64TripleA_353 : Nat.Prime 353 := by norm_num
private theorem prime_free64TripleA_373 : Nat.Prime 373 := by norm_num
private theorem prime_free64TripleA_389 : Nat.Prime 389 := by norm_num
private theorem prime_free64TripleA_463 : Nat.Prime 463 := by norm_num
private theorem prime_free64TripleA_487 : Nat.Prime 487 := by norm_num
private theorem prime_free64TripleA_503 : Nat.Prime 503 := by norm_num
private theorem prime_free64TripleA_509 : Nat.Prime 509 := by norm_num
private theorem prime_free64TripleA_541 : Nat.Prime 541 := by norm_num
private theorem prime_free64TripleA_547 : Nat.Prime 547 := by norm_num
private theorem prime_free64TripleA_569 : Nat.Prime 569 := by norm_num
private theorem prime_free64TripleA_727 : Nat.Prime 727 := by norm_num
private theorem prime_free64TripleA_733 : Nat.Prime 733 := by norm_num
private theorem prime_free64TripleA_739 : Nat.Prime 739 := by norm_num
private theorem prime_free64TripleA_769 : Nat.Prime 769 := by norm_num
private theorem prime_free64TripleA_809 : Nat.Prime 809 := by norm_num
private theorem prime_free64TripleA_811 : Nat.Prime 811 := by norm_num
private theorem prime_free64TripleA_821 : Nat.Prime 821 := by norm_num
private theorem prime_free64TripleA_823 : Nat.Prime 823 := by norm_num
private theorem prime_free64TripleA_839 : Nat.Prime 839 := by norm_num
private theorem prime_free64TripleA_887 : Nat.Prime 887 := by norm_num
private theorem prime_free64TripleA_929 : Nat.Prime 929 := by norm_num
private theorem prime_free64TripleA_967 : Nat.Prime 967 := by norm_num
private theorem prime_free64TripleA_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_free64TripleA_1171 : Nat.Prime 1171 := by norm_num
private theorem prime_free64TripleA_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_free64TripleA_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_free64TripleA_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_free64TripleA_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_free64TripleA_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_free64TripleA_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_free64TripleA_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_free64TripleA_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_free64TripleA_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_free64TripleA_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_free64TripleA_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_free64TripleA_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_free64TripleA_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_free64TripleA_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_free64TripleA_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_free64TripleA_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_free64TripleA_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_free64TripleA_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_free64TripleA_2383 : Nat.Prime 2383 := by norm_num
private theorem prime_free64TripleA_2549 : Nat.Prime 2549 := by norm_num
private theorem prime_free64TripleA_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_free64TripleA_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_free64TripleA_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_free64TripleA_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_free64TripleA_3469 : Nat.Prime 3469 := by norm_num
private theorem prime_free64TripleA_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_free64TripleA_3833 : Nat.Prime 3833 := by norm_num
private theorem prime_free64TripleA_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_free64TripleA_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_free64TripleA_4139 : Nat.Prime 4139 := by norm_num
private theorem prime_free64TripleA_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_free64TripleA_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_free64TripleA_4373 : Nat.Prime 4373 := by norm_num
private theorem prime_free64TripleA_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_free64TripleA_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_free64TripleA_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_free64TripleA_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_free64TripleA_5501 : Nat.Prime 5501 := by norm_num
private theorem prime_free64TripleA_5639 : Nat.Prime 5639 := by norm_num
private theorem prime_free64TripleA_6113 : Nat.Prime 6113 := by norm_num
private theorem prime_free64TripleA_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_free64TripleA_6803 : Nat.Prime 6803 := by norm_num
private theorem prime_free64TripleA_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_free64TripleA_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_free64TripleA_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_free64TripleA_8537 : Nat.Prime 8537 := by norm_num
private theorem prime_free64TripleA_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_free64TripleA_9539 : Nat.Prime 9539 := by norm_num
private theorem prime_free64TripleA_9547 : Nat.Prime 9547 := by norm_num
private theorem prime_free64TripleA_9767 : Nat.Prime 9767 := by norm_num
private theorem prime_free64TripleA_10531 : Nat.Prime 10531 := by norm_num
private theorem prime_free64TripleA_11083 : Nat.Prime 11083 := by norm_num
private theorem prime_free64TripleA_12113 : Nat.Prime 12113 := by norm_num
private theorem prime_free64TripleA_12799 : Nat.Prime 12799 := by norm_num
private theorem prime_free64TripleA_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_free64TripleA_13963 : Nat.Prime 13963 := by norm_num
private theorem prime_free64TripleA_14251 : Nat.Prime 14251 := by norm_num
private theorem prime_free64TripleA_14627 : Nat.Prime 14627 := by norm_num
private theorem prime_free64TripleA_14851 : Nat.Prime 14851 := by norm_num
private theorem prime_free64TripleA_15013 : Nat.Prime 15013 := by norm_num
private theorem prime_free64TripleA_15493 : Nat.Prime 15493 := by norm_num
private theorem prime_free64TripleA_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_free64TripleA_16747 : Nat.Prime 16747 := by norm_num
private theorem prime_free64TripleA_17761 : Nat.Prime 17761 := by norm_num
private theorem prime_free64TripleA_18133 : Nat.Prime 18133 := by norm_num
private theorem prime_free64TripleA_19139 : Nat.Prime 19139 := by norm_num
private theorem prime_free64TripleA_20929 : Nat.Prime 20929 := by norm_num
private theorem prime_free64TripleA_21011 : Nat.Prime 21011 := by norm_num
private theorem prime_free64TripleA_21821 : Nat.Prime 21821 := by norm_num
private theorem prime_free64TripleA_22343 : Nat.Prime 22343 := by norm_num
private theorem prime_free64TripleA_22573 : Nat.Prime 22573 := by norm_num
private theorem prime_free64TripleA_22963 : Nat.Prime 22963 := by norm_num
private theorem prime_free64TripleA_26189 : Nat.Prime 26189 := by norm_num
private theorem prime_free64TripleA_27127 : Nat.Prime 27127 := by norm_num
private theorem prime_free64TripleA_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_free64TripleA_36313 : Nat.Prime 36313 := by norm_num
private theorem prime_free64TripleA_44203 : Nat.Prime 44203 := by norm_num
private theorem prime_free64TripleA_54049 : Nat.Prime 54049 := by norm_num
private theorem prime_free64TripleA_55249 : Nat.Prime 55249 := by norm_num
private theorem prime_free64TripleA_56687 : Nat.Prime 56687 := by norm_num
private theorem prime_free64TripleA_57881 : Nat.Prime 57881 := by norm_num
private theorem prime_free64TripleA_59207 : Nat.Prime 59207 := by norm_num
private theorem prime_free64TripleA_60457 : Nat.Prime 60457 := by norm_num
private theorem prime_free64TripleA_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_free64TripleA_62761 : Nat.Prime 62761 := by norm_num
private theorem prime_free64TripleA_62981 : Nat.Prime 62981 := by norm_num
private theorem prime_free64TripleA_67537 : Nat.Prime 67537 := by norm_num
private theorem prime_free64TripleA_76829 : Nat.Prime 76829 := by norm_num
private theorem prime_free64TripleA_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_free64TripleA_81331 : Nat.Prime 81331 := by norm_num
private theorem prime_free64TripleA_82529 : Nat.Prime 82529 := by norm_num
private theorem prime_free64TripleA_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_free64TripleA_94771 : Nat.Prime 94771 := by norm_num
private theorem prime_free64TripleA_97961 : Nat.Prime 97961 := by norm_num
private theorem prime_free64TripleA_101501 : Nat.Prime 101501 := by norm_num
private theorem prime_free64TripleA_101963 : Nat.Prime 101963 := by norm_num
private theorem prime_free64TripleA_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_free64TripleA_141551 : Nat.Prime 141551 := by norm_num
private theorem prime_free64TripleA_143159 : Nat.Prime 143159 := by norm_num
private theorem prime_free64TripleA_144071 : Nat.Prime 144071 := by norm_num
private theorem prime_free64TripleA_144589 : Nat.Prime 144589 := by norm_num
private theorem prime_free64TripleA_150869 : Nat.Prime 150869 := by norm_num
private theorem prime_free64TripleA_152441 : Nat.Prime 152441 := by norm_num
private theorem prime_free64TripleA_153089 : Nat.Prime 153089 := by norm_num
private theorem prime_free64TripleA_157429 : Nat.Prime 157429 := by norm_num
private theorem prime_free64TripleA_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_free64TripleA_180533 : Nat.Prime 180533 := by norm_num
private theorem prime_free64TripleA_181549 : Nat.Prime 181549 := by norm_num
private theorem prime_free64TripleA_186799 : Nat.Prime 186799 := by norm_num
private theorem prime_free64TripleA_192263 : Nat.Prime 192263 := by norm_num
private theorem prime_free64TripleA_194867 : Nat.Prime 194867 := by norm_num
private theorem prime_free64TripleA_197359 : Nat.Prime 197359 := by norm_num
private theorem prime_free64TripleA_204749 : Nat.Prime 204749 := by norm_num
private theorem prime_free64TripleA_215447 : Nat.Prime 215447 := by norm_num
private theorem prime_free64TripleA_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_free64TripleA_240017 : Nat.Prime 240017 := by norm_num
private theorem prime_free64TripleA_260003 : Nat.Prime 260003 := by norm_num
private theorem prime_free64TripleA_323801 : Nat.Prime 323801 := by norm_num
private theorem prime_free64TripleA_339389 : Nat.Prime 339389 := by norm_num
private theorem prime_free64TripleA_365159 : Nat.Prime 365159 := by norm_num
private theorem prime_free64TripleA_378559 : Nat.Prime 378559 := by norm_num
private theorem prime_free64TripleA_411013 : Nat.Prime 411013 := by norm_num
private theorem prime_free64TripleA_418069 : Nat.Prime 418069 := by norm_num
private theorem prime_free64TripleA_441499 : Nat.Prime 441499 := by norm_num
private theorem prime_free64TripleA_443017 : Nat.Prime 443017 := by norm_num
private theorem prime_free64TripleA_472123 : Nat.Prime 472123 := by norm_num
private theorem prime_free64TripleA_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_free64TripleA_528991 : Nat.Prime 528991 := by norm_num
private theorem prime_free64TripleA_545911 : Nat.Prime 545911 := by norm_num
private theorem prime_free64TripleA_561521 : Nat.Prime 561521 := by norm_num
private theorem prime_free64TripleA_587633 : Nat.Prime 587633 := by norm_num
private theorem prime_free64TripleA_665591 : Nat.Prime 665591 := by norm_num
private theorem prime_free64TripleA_680293 : Nat.Prime 680293 := by norm_num
private theorem prime_free64TripleA_710683 : Nat.Prime 710683 := by norm_num
private theorem prime_free64TripleA_745709 : Nat.Prime 745709 := by norm_num
private theorem prime_free64TripleA_773027 : Nat.Prime 773027 := by norm_num
private theorem prime_free64TripleA_889351 : Nat.Prime 889351 := by norm_num
private theorem prime_free64TripleA_953221 : Nat.Prime 953221 := by norm_num
private theorem prime_free64TripleA_1034941 : Nat.Prime 1034941 := by norm_num
private theorem prime_free64TripleA_1208521 : Nat.Prime 1208521 := by norm_num
private theorem prime_free64TripleA_1244879 : Nat.Prime 1244879 := by norm_num
private theorem prime_free64TripleA_1262869 : Nat.Prime 1262869 := by norm_num
private theorem prime_free64TripleA_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_free64TripleA_1538233 : Nat.Prime 1538233 := by norm_num
private theorem prime_free64TripleA_1540031 : Nat.Prime 1540031 := by norm_num
private theorem prime_free64TripleA_1585469 : Nat.Prime 1585469 := by norm_num
private theorem prime_free64TripleA_1630897 : Nat.Prime 1630897 := by norm_num
private theorem prime_free64TripleA_1796567 : Nat.Prime 1796567 := by norm_num
private theorem prime_free64TripleA_1915267 : Nat.Prime 1915267 := by norm_num
private theorem prime_free64TripleA_1967417 : Nat.Prime 1967417 := by norm_num
private theorem prime_free64TripleA_2217799 : Nat.Prime 2217799 := by norm_num
private theorem prime_free64TripleA_2272973 : Nat.Prime 2272973 := by norm_num
private theorem prime_free64TripleA_2327483 : Nat.Prime 2327483 := by norm_num
private theorem prime_free64TripleA_2424967 : Nat.Prime 2424967 := by norm_num
private theorem prime_free64TripleA_2892119 : Nat.Prime 2892119 := by norm_num
private theorem prime_free64TripleA_2940799 : Nat.Prime 2940799 := by norm_num
private theorem prime_free64TripleA_2965093 : Nat.Prime 2965093 := by norm_num
private theorem prime_free64TripleA_2971499 : Nat.Prime 2971499 := by norm_num
private theorem prime_free64TripleA_3047861 : Nat.Prime 3047861 := by norm_num
private theorem prime_free64TripleA_3363887 : Nat.Prime 3363887 := by norm_num
private theorem prime_free64TripleA_3473291 : Nat.Prime 3473291 := by norm_num
private theorem prime_free64TripleA_3911497 : Nat.Prime 3911497 := by norm_num
private theorem prime_free64TripleA_3962843 : Nat.Prime 3962843 := by norm_num
private theorem prime_free64TripleA_4086109 : Nat.Prime 4086109 := by norm_num
private theorem prime_free64TripleA_4138139 : Nat.Prime 4138139 := by norm_num
private theorem prime_free64TripleA_4359517 : Nat.Prime 4359517 := by norm_num
private theorem prime_free64TripleA_4597709 : Nat.Prime 4597709 := by norm_num
private theorem prime_free64TripleA_5054317 : Nat.Prime 5054317 := by norm_num
private theorem prime_free64TripleA_6618487 : Nat.Prime 6618487 := by norm_num
private theorem prime_free64TripleA_7076143 : Nat.Prime 7076143 := by norm_num
private theorem prime_free64TripleA_7208693 : Nat.Prime 7208693 := by norm_num
private theorem prime_free64TripleA_7290853 : Nat.Prime 7290853 := by norm_num
private theorem prime_free64TripleA_7316849 : Nat.Prime 7316849 := by norm_num
private theorem prime_free64TripleA_7819681 : Nat.Prime 7819681 := by norm_num
private theorem prime_free64TripleA_7982567 : Nat.Prime 7982567 := by norm_num
private theorem prime_free64TripleA_8197093 : Nat.Prime 8197093 := by norm_num
private theorem prime_free64TripleA_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_free64TripleA_8506039 : Nat.Prime 8506039 := by norm_num
private theorem prime_free64TripleA_9792301 : Nat.Prime 9792301 := by norm_num

private theorem prime_free64TripleA_10135121 : Nat.Prime 10135121 := by
  have hfermat : (3 : ZMod 10135121) ^ (10135121 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10135121) ^ ((10135121 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10135121) ^ ((10135121 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10135121) ^ ((10135121 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10135121) ^ ((10135121 - 1) / 839) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10135121 (3 : ZMod 10135121)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (151, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (151, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod = 10135121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64TripleA_151
      · exact prime_free64TripleA_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_15295123 : Nat.Prime 15295123 := by
  have hfermat : (2 : ZMod 15295123) ^ (15295123 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15295123) ^ ((15295123 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15295123) ^ ((15295123 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15295123) ^ ((15295123 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 15295123) ^ ((15295123 - 1) / 9767) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15295123 (2 : ZMod 15295123)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (29, 1), (9767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (29, 1), (9767, 1)] : List FactorBlock).map factorBlockValue).prod = 15295123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_29
      · exact prime_free64TripleA_9767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_40346827 : Nat.Prime 40346827 := by
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
      · exact prime_free64TripleA_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_92147537 : Nat.Prime 92147537 := by
  have hfermat : (3 : ZMod 92147537) ^ (92147537 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 92147537) ^ ((92147537 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 92147537) ^ ((92147537 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 92147537) ^ ((92147537 - 1) / 443017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 92147537 (3 : ZMod 92147537)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (443017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (443017, 1)] : List FactorBlock).map factorBlockValue).prod = 92147537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64TripleA_443017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_107413291 : Nat.Prime 107413291 := by
  have hfermat : (3 : ZMod 107413291) ^ (107413291 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 107413291) ^ ((107413291 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 107413291) ^ ((107413291 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 107413291) ^ ((107413291 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 107413291) ^ ((107413291 - 1) / 44203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 107413291 (3 : ZMod 107413291)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (5, 1), (44203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (5, 1), (44203, 1)] : List FactorBlock).map factorBlockValue).prod = 107413291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64TripleA_44203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_171370811 : Nat.Prime 171370811 := by
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
      · exact prime_free64TripleA_22343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_17678041 : Nat.Prime 17678041 := by
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
      · exact prime_free64TripleA_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_176780411 : Nat.Prime 176780411 := by
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
      · exact prime_free64TripleA_17678041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_197435923 : Nat.Prime 197435923 := by
  have hfermat : (5 : ZMod 197435923) ^ (197435923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 197435923) ^ ((197435923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 197435923) ^ ((197435923 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 197435923) ^ ((197435923 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 197435923) ^ ((197435923 - 1) / 889351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 197435923 (5 : ZMod 197435923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (37, 1), (889351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (37, 1), (889351, 1)] : List FactorBlock).map factorBlockValue).prod = 197435923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_free64TripleA_889351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_236499493 : Nat.Prime 236499493 := by
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
      · exact prime_free64TripleA_6803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_245696267 : Nat.Prime 245696267 := by
  have hfermat : (2 : ZMod 245696267) ^ (245696267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 245696267) ^ ((245696267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 245696267) ^ ((245696267 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 245696267) ^ ((245696267 - 1) / 3962843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 245696267 (2 : ZMod 245696267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (3962843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (3962843, 1)] : List FactorBlock).map factorBlockValue).prod = 245696267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64TripleA_3962843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_17885311 : Nat.Prime 17885311 := by
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
      · exact prime_free64TripleA_3089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_321935599 : Nat.Prime 321935599 := by
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
      · exact prime_free64TripleA_17885311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_370033847 : Nat.Prime 370033847 := by
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
      · exact prime_free64TripleA_14627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_436680877 : Nat.Prime 436680877 := by
  have hfermat : (5 : ZMod 436680877) ^ (436680877 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 436680877) ^ ((436680877 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 436680877) ^ ((436680877 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 436680877) ^ ((436680877 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 436680877) ^ ((436680877 - 1) / 1915267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 436680877 (5 : ZMod 436680877)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (19, 1), (1915267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (19, 1), (1915267, 1)] : List FactorBlock).map factorBlockValue).prod = 436680877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_free64TripleA_1915267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_464968781 : Nat.Prime 464968781 := by
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
      · exact prime_free64TripleA_131
      · exact prime_free64TripleA_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_222982297 : Nat.Prime 222982297 := by
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
      · exact prime_free64TripleA_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_891929189 : Nat.Prime 891929189 := by
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
      · exact prime_free64TripleA_222982297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64TripleA_979501163 : Nat.Prime 979501163 := by
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
      · exact prime_free64TripleA_1787
      · exact prime_free64TripleA_5171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_13372327 : Nat.Prime 13372327 := by
  have hfermat : (6 : ZMod 13372327) ^ (13372327 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 13372327) ^ ((13372327 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 13372327) ^ ((13372327 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 13372327) ^ ((13372327 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 13372327) ^ ((13372327 - 1) / 67537) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13372327 (6 : ZMod 13372327)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (67537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (67537, 1)] : List FactorBlock).map factorBlockValue).prod = 13372327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64TripleA_67537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_1577934587 : Nat.Prime 1577934587 := by
  have hfermat : (2 : ZMod 1577934587) ^ (1577934587 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1577934587) ^ ((1577934587 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1577934587) ^ ((1577934587 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1577934587) ^ ((1577934587 - 1) / 13372327) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1577934587 (2 : ZMod 1577934587)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (13372327, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (13372327, 1)] : List FactorBlock).map factorBlockValue).prod = 1577934587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_free64TripleA_13372327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_2046113681 : Nat.Prime 2046113681 := by
  have hfermat : (3 : ZMod 2046113681) ^ (2046113681 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2046113681) ^ ((2046113681 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2046113681) ^ ((2046113681 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2046113681) ^ ((2046113681 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2046113681) ^ ((2046113681 - 1) / 1967417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2046113681 (3 : ZMod 2046113681)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (13, 1), (1967417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (13, 1), (1967417, 1)] : List FactorBlock).map factorBlockValue).prod = 2046113681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64TripleA_1967417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_13311821 : Nat.Prime 13311821 := by
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
      · exact prime_free64TripleA_665591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_2076644077 : Nat.Prime 2076644077 := by
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
      · exact prime_free64TripleA_13311821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_84294913 : Nat.Prime 84294913 := by
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
      · exact prime_free64TripleA_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_3540386347 : Nat.Prime 3540386347 := by
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
      · exact prime_free64TripleA_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_3561523789 : Nat.Prime 3561523789 := by
  have hfermat : (2 : ZMod 3561523789) ^ (3561523789 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3561523789) ^ ((3561523789 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3561523789) ^ ((3561523789 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3561523789) ^ ((3561523789 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3561523789) ^ ((3561523789 - 1) / 463) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 3561523789) ^ ((3561523789 - 1) / 4679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3561523789 (2 : ZMod 3561523789)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (137, 1), (463, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (137, 1), (463, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod = 3561523789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_137
      · exact prime_free64TripleA_463
      · exact prime_free64TripleA_4679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_3726729229 : Nat.Prime 3726729229 := by
  have hfermat : (2 : ZMod 3726729229) ^ (3726729229 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3726729229) ^ ((3726729229 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3726729229) ^ ((3726729229 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3726729229) ^ ((3726729229 - 1) / 269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3726729229) ^ ((3726729229 - 1) / 569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 3726729229) ^ ((3726729229 - 1) / 2029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3726729229 (2 : ZMod 3726729229)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (269, 1), (569, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (269, 1), (569, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod = 3726729229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_269
      · exact prime_free64TripleA_569
      · exact prime_free64TripleA_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_6391408799 : Nat.Prime 6391408799 := by
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
      · exact prime_free64TripleA_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_6442882141 : Nat.Prime 6442882141 := by
  have hfermat : (7 : ZMod 6442882141) ^ (6442882141 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 6442882141) ^ ((6442882141 - 1) / 1259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6442882141 (7 : ZMod 6442882141)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (19, 1), (67, 2), (1259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (19, 1), (67, 2), (1259, 1)] : List FactorBlock).map factorBlockValue).prod = 6442882141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_67
      · exact prime_free64TripleA_1259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_11237539 : Nat.Prime 11237539 := by
  have hfermat : (3 : ZMod 11237539) ^ (11237539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11237539) ^ ((11237539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11237539) ^ ((11237539 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11237539) ^ ((11237539 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11237539) ^ ((11237539 - 1) / 144071) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11237539 (3 : ZMod 11237539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (144071, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (144071, 1)] : List FactorBlock).map factorBlockValue).prod = 11237539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64TripleA_144071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_6540247699 : Nat.Prime 6540247699 := by
  have hfermat : (2 : ZMod 6540247699) ^ (6540247699 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 6540247699) ^ ((6540247699 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 6540247699) ^ ((6540247699 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 6540247699) ^ ((6540247699 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 6540247699) ^ ((6540247699 - 1) / 11237539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6540247699 (2 : ZMod 6540247699)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (97, 1), (11237539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (97, 1), (11237539, 1)] : List FactorBlock).map factorBlockValue).prod = 6540247699 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_97
      · exact prime_free64TripleA_11237539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_7987921657 : Nat.Prime 7987921657 := by
  have hfermat : (15 : ZMod 7987921657) ^ (7987921657 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (15 : ZMod 7987921657) ^ ((7987921657 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (15 : ZMod 7987921657) ^ ((7987921657 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (15 : ZMod 7987921657) ^ ((7987921657 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (15 : ZMod 7987921657) ^ ((7987921657 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (15 : ZMod 7987921657) ^ ((7987921657 - 1) / 2327483) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7987921657 (15 : ZMod 7987921657)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (13, 1), (2327483, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (13, 1), (2327483, 1)] : List FactorBlock).map factorBlockValue).prod = 7987921657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_free64TripleA_2327483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_9257799907 : Nat.Prime 9257799907 := by
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
      · exact prime_free64TripleA_94771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_235217063 : Nat.Prime 235217063 := by
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
      · exact prime_free64TripleA_541
      · exact prime_free64TripleA_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_9879116647 : Nat.Prime 9879116647 := by
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
      · exact prime_free64TripleA_235217063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_198251509 : Nat.Prime 198251509 := by
  have hfermat : (18 : ZMod 198251509) ^ (198251509 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (18 : ZMod 198251509) ^ ((198251509 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (18 : ZMod 198251509) ^ ((198251509 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (18 : ZMod 198251509) ^ ((198251509 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (18 : ZMod 198251509) ^ ((198251509 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (18 : ZMod 198251509) ^ ((198251509 - 1) / 181549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 198251509 (18 : ZMod 198251509)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (13, 1), (181549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (13, 1), (181549, 1)] : List FactorBlock).map factorBlockValue).prod = 198251509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_free64TripleA_181549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_15463617703 : Nat.Prime 15463617703 := by
  have hfermat : (5 : ZMod 15463617703) ^ (15463617703 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 15463617703) ^ ((15463617703 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 15463617703) ^ ((15463617703 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 15463617703) ^ ((15463617703 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 15463617703) ^ ((15463617703 - 1) / 198251509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15463617703 (5 : ZMod 15463617703)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (198251509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (198251509, 1)] : List FactorBlock).map factorBlockValue).prod = 15463617703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64TripleA_198251509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_20250214969 : Nat.Prime 20250214969 := by
  have hfermat : (14 : ZMod 20250214969) ^ (20250214969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 20250214969) ^ ((20250214969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 20250214969) ^ ((20250214969 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 20250214969) ^ ((20250214969 - 1) / 14251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 20250214969) ^ ((20250214969 - 1) / 59207) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20250214969 (14 : ZMod 20250214969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (14251, 1), (59207, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (14251, 1), (59207, 1)] : List FactorBlock).map factorBlockValue).prod = 20250214969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_14251
      · exact prime_free64TripleA_59207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_19107623 : Nat.Prime 19107623 := by
  have hfermat : (5 : ZMod 19107623) ^ (19107623 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 19107623) ^ ((19107623 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 19107623) ^ ((19107623 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 19107623) ^ ((19107623 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 19107623) ^ ((19107623 - 1) / 1433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19107623 (5 : ZMod 19107623)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (59, 1), (113, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (59, 1), (113, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod = 19107623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_59
      · exact prime_t64_113
      · exact prime_free64TripleA_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_21018385301 : Nat.Prime 21018385301 := by
  have hfermat : (2 : ZMod 21018385301) ^ (21018385301 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 21018385301) ^ ((21018385301 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 21018385301) ^ ((21018385301 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 21018385301) ^ ((21018385301 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 21018385301) ^ ((21018385301 - 1) / 19107623) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21018385301 (2 : ZMod 21018385301)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (11, 1), (19107623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (11, 1), (19107623, 1)] : List FactorBlock).map factorBlockValue).prod = 21018385301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64TripleA_19107623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_42857783 : Nat.Prime 42857783 := by
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
      · exact prime_free64TripleA_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_30429025931 : Nat.Prime 30429025931 := by
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
      · exact prime_free64TripleA_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_50054507627 : Nat.Prime 50054507627 := by
  have hfermat : (2 : ZMod 50054507627) ^ (50054507627 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 50054507627) ^ ((50054507627 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 50054507627) ^ ((50054507627 - 1) / 56687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 50054507627) ^ ((50054507627 - 1) / 441499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 50054507627 (2 : ZMod 50054507627)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (56687, 1), (441499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (56687, 1), (441499, 1)] : List FactorBlock).map factorBlockValue).prod = 50054507627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64TripleA_56687
      · exact prime_free64TripleA_441499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_127114246817 : Nat.Prime 127114246817 := by
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
      · exact prime_free64TripleA_8506039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_263800094039 : Nat.Prime 263800094039 := by
  have hfermat : (11 : ZMod 263800094039) ^ (263800094039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 263800094039) ^ ((263800094039 - 1) / 1051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 263800094039 (11 : ZMod 263800094039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 2), (23, 1), (83, 1), (389, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 2), (23, 1), (83, 1), (389, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod = 263800094039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_t64_83
      · exact prime_free64TripleA_389
      · exact prime_t64_1051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_277508030299 : Nat.Prime 277508030299 := by
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
      · exact prime_free64TripleA_1429
      · exact prime_free64TripleA_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_381637835351 : Nat.Prime 381637835351 := by
  have hfermat : (11 : ZMod 381637835351) ^ (381637835351 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 381637835351) ^ ((381637835351 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 381637835351) ^ ((381637835351 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 381637835351) ^ ((381637835351 - 1) / 191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 381637835351) ^ ((381637835351 - 1) / 661) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 381637835351) ^ ((381637835351 - 1) / 60457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 381637835351 (11 : ZMod 381637835351)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (191, 1), (661, 1), (60457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (191, 1), (661, 1), (60457, 1)] : List FactorBlock).map factorBlockValue).prod = 381637835351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_191
      · exact prime_t64_661
      · exact prime_free64TripleA_60457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_400597142329 : Nat.Prime 400597142329 := by
  have hfermat : (11 : ZMod 400597142329) ^ (400597142329 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 400597142329) ^ ((400597142329 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 400597142329) ^ ((400597142329 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 400597142329) ^ ((400597142329 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 400597142329) ^ ((400597142329 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 400597142329) ^ ((400597142329 - 1) / 7982567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 400597142329 (11 : ZMod 400597142329)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (17, 1), (41, 1), (7982567, 1)] : List FactorBlock).map factorBlockValue).prod = 400597142329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_free64TripleA_7982567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_9277522589 : Nat.Prime 9277522589 := by
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
      · exact prime_free64TripleA_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_964862349257 : Nat.Prime 964862349257 := by
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
      · exact prime_free64TripleA_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_1128574980601 : Nat.Prime 1128574980601 := by
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
      · exact prime_free64TripleA_13009
      · exact prime_free64TripleA_144589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_1694722097147 : Nat.Prime 1694722097147 := by
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
      · exact prime_free64TripleA_62981
      · exact prime_free64TripleA_1034941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_16905180671 : Nat.Prime 16905180671 := by
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
      · exact prime_free64TripleA_1538233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_5206795646669 : Nat.Prime 5206795646669 := by
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
      · exact prime_free64TripleA_16905180671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_10913076631 : Nat.Prime 10913076631 := by
  have hfermat : (6 : ZMod 10913076631) ^ (10913076631 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 10913076631) ^ ((10913076631 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 10913076631) ^ ((10913076631 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 10913076631) ^ ((10913076631 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 10913076631) ^ ((10913076631 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 10913076631) ^ ((10913076631 - 1) / 3911497) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10913076631 (6 : ZMod 10913076631)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (31, 1), (3911497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (31, 1), (3911497, 1)] : List FactorBlock).map factorBlockValue).prod = 10913076631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_free64TripleA_3911497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_6853412124269 : Nat.Prime 6853412124269 := by
  have hfermat : (2 : ZMod 6853412124269) ^ (6853412124269 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 6853412124269) ^ ((6853412124269 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 6853412124269) ^ ((6853412124269 - 1) / 157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 6853412124269) ^ ((6853412124269 - 1) / 10913076631) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6853412124269 (2 : ZMod 6853412124269)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (157, 1), (10913076631, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (157, 1), (10913076631, 1)] : List FactorBlock).map factorBlockValue).prod = 6853412124269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_157
      · exact prime_free64TripleA_10913076631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_6859902452969 : Nat.Prime 6859902452969 := by
  have hfermat : (3 : ZMod 6859902452969) ^ (6859902452969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 6859902452969) ^ ((6859902452969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 6859902452969) ^ ((6859902452969 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 6859902452969) ^ ((6859902452969 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 6859902452969) ^ ((6859902452969 - 1) / 26189) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 6859902452969) ^ ((6859902452969 - 1) / 27127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6859902452969 (3 : ZMod 6859902452969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (71, 1), (26189, 1), (27127, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (71, 1), (26189, 1), (27127, 1)] : List FactorBlock).map factorBlockValue).prod = 6859902452969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_71
      · exact prime_free64TripleA_26189
      · exact prime_free64TripleA_27127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_59336393 : Nat.Prime 59336393 := by
  have hfermat : (3 : ZMod 59336393) ^ (59336393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 59336393) ^ ((59336393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 59336393) ^ ((59336393 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 59336393) ^ ((59336393 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 59336393) ^ ((59336393 - 1) / 22963) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 59336393 (3 : ZMod 59336393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (19, 1), (22963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (19, 1), (22963, 1)] : List FactorBlock).map factorBlockValue).prod = 59336393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_free64TripleA_22963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_6928473265039 : Nat.Prime 6928473265039 := by
  have hfermat : (3 : ZMod 6928473265039) ^ (6928473265039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 6928473265039) ^ ((6928473265039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 6928473265039) ^ ((6928473265039 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 6928473265039) ^ ((6928473265039 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 6928473265039) ^ ((6928473265039 - 1) / 499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 6928473265039) ^ ((6928473265039 - 1) / 59336393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6928473265039 (3 : ZMod 6928473265039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (13, 1), (499, 1), (59336393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (13, 1), (499, 1), (59336393, 1)] : List FactorBlock).map factorBlockValue).prod = 6928473265039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_499
      · exact prime_free64TripleA_59336393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_22834853 : Nat.Prime 22834853 := by
  have hfermat : (2 : ZMod 22834853) ^ (22834853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 22834853) ^ ((22834853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 22834853) ^ ((22834853 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 22834853) ^ ((22834853 - 1) / 28687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 22834853 (2 : ZMod 22834853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (199, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (199, 1), (28687, 1)] : List FactorBlock).map factorBlockValue).prod = 22834853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64TripleA_199
      · exact prime_free64TripleA_28687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_8160719765141 : Nat.Prime 8160719765141 := by
  have hfermat : (3 : ZMod 8160719765141) ^ (8160719765141 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 8160719765141) ^ ((8160719765141 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 8160719765141) ^ ((8160719765141 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 8160719765141) ^ ((8160719765141 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 8160719765141) ^ ((8160719765141 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 8160719765141) ^ ((8160719765141 - 1) / 22834853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8160719765141 (3 : ZMod 8160719765141)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (107, 1), (167, 1), (22834853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (107, 1), (167, 1), (22834853, 1)] : List FactorBlock).map factorBlockValue).prod = 8160719765141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_t64_167
      · exact prime_free64TripleA_22834853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_166895539 : Nat.Prime 166895539 := by
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
      · exact prime_free64TripleA_1873
      · exact prime_free64TripleA_14851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_33484585780649 : Nat.Prime 33484585780649 := by
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
      · exact prime_free64TripleA_809
      · exact prime_free64TripleA_166895539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_52107281 : Nat.Prime 52107281 := by
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
      · exact prime_free64TripleA_21011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_39117456919511 : Nat.Prime 39117456919511 := by
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
      · exact prime_free64TripleA_1831
      · exact prime_free64TripleA_52107281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_4910415379 : Nat.Prime 4910415379 := by
  have hfermat : (2 : ZMod 4910415379) ^ (4910415379 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4910415379) ^ ((4910415379 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4910415379) ^ ((4910415379 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4910415379) ^ ((4910415379 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 4910415379) ^ ((4910415379 - 1) / 733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 4910415379) ^ ((4910415379 - 1) / 101501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4910415379 (2 : ZMod 4910415379)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (733, 1), (101501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (733, 1), (101501, 1)] : List FactorBlock).map factorBlockValue).prod = 4910415379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64TripleA_733
      · exact prime_free64TripleA_101501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_726741476093 : Nat.Prime 726741476093 := by
  have hfermat : (2 : ZMod 726741476093) ^ (726741476093 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 726741476093) ^ ((726741476093 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 726741476093) ^ ((726741476093 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 726741476093) ^ ((726741476093 - 1) / 4910415379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 726741476093 (2 : ZMod 726741476093)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (4910415379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (4910415379, 1)] : List FactorBlock).map factorBlockValue).prod = 726741476093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_free64TripleA_4910415379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_61046283991813 : Nat.Prime 61046283991813 := by
  have hfermat : (6 : ZMod 61046283991813) ^ (61046283991813 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 61046283991813) ^ ((61046283991813 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 61046283991813) ^ ((61046283991813 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 61046283991813) ^ ((61046283991813 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 61046283991813) ^ ((61046283991813 - 1) / 726741476093) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 61046283991813 (6 : ZMod 61046283991813)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (726741476093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (726741476093, 1)] : List FactorBlock).map factorBlockValue).prod = 61046283991813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64TripleA_726741476093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_75391139 : Nat.Prime 75391139 := by
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
      · exact prime_free64TripleA_197359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_71425565088601 : Nat.Prime 71425565088601 := by
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
      · exact prime_free64TripleA_75391139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_751061057 : Nat.Prime 751061057 := by
  have hfermat : (3 : ZMod 751061057) ^ (751061057 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 751061057) ^ ((751061057 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 751061057) ^ ((751061057 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 751061057) ^ ((751061057 - 1) / 378559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 751061057 (3 : ZMod 751061057)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (31, 1), (378559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (31, 1), (378559, 1)] : List FactorBlock).map factorBlockValue).prod = 751061057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64TripleA_378559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_2020354243331 : Nat.Prime 2020354243331 := by
  have hfermat : (2 : ZMod 2020354243331) ^ (2020354243331 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2020354243331) ^ ((2020354243331 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2020354243331) ^ ((2020354243331 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2020354243331) ^ ((2020354243331 - 1) / 269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2020354243331) ^ ((2020354243331 - 1) / 751061057) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2020354243331 (2 : ZMod 2020354243331)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (269, 1), (751061057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (269, 1), (751061057, 1)] : List FactorBlock).map factorBlockValue).prod = 2020354243331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_269
      · exact prime_free64TripleA_751061057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_101017712166551 : Nat.Prime 101017712166551 := by
  have hfermat : (11 : ZMod 101017712166551) ^ (101017712166551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 101017712166551) ^ ((101017712166551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 101017712166551) ^ ((101017712166551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 101017712166551) ^ ((101017712166551 - 1) / 2020354243331) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 101017712166551 (11 : ZMod 101017712166551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (2020354243331, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (2020354243331, 1)] : List FactorBlock).map factorBlockValue).prod = 101017712166551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64TripleA_2020354243331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_146789130460481 : Nat.Prime 146789130460481 := by
  have hfermat : (3 : ZMod 146789130460481) ^ (146789130460481 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 146789130460481) ^ ((146789130460481 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 146789130460481) ^ ((146789130460481 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 146789130460481) ^ ((146789130460481 - 1) / 1051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 146789130460481) ^ ((146789130460481 - 1) / 2851) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 146789130460481) ^ ((146789130460481 - 1) / 153089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 146789130460481 (3 : ZMod 146789130460481)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (1051, 1), (2851, 1), (153089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (1051, 1), (2851, 1), (153089, 1)] : List FactorBlock).map factorBlockValue).prod = 146789130460481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_1051
      · exact prime_free64TripleA_2851
      · exact prime_free64TripleA_153089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_176908313113559 : Nat.Prime 176908313113559 := by
  have hfermat : (11 : ZMod 176908313113559) ^ (176908313113559 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 9547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 176908313113559) ^ ((176908313113559 - 1) / 1630897) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 176908313113559 (11 : ZMod 176908313113559)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (19, 1), (23, 1), (9547, 1), (1630897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (19, 1), (23, 1), (9547, 1), (1630897, 1)] : List FactorBlock).map factorBlockValue).prod = 176908313113559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_free64TripleA_9547
      · exact prime_free64TripleA_1630897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_233840303 : Nat.Prime 233840303 := by
  have hfermat : (5 : ZMod 233840303) ^ (233840303 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 233840303) ^ ((233840303 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 233840303) ^ ((233840303 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 233840303) ^ ((233840303 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 233840303) ^ ((233840303 - 1) / 19139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 233840303 (5 : ZMod 233840303)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (149, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (149, 1), (19139, 1)] : List FactorBlock).map factorBlockValue).prod = 233840303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_t64_149
      · exact prime_free64TripleA_19139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_230653527350717 : Nat.Prime 230653527350717 := by
  have hfermat : (2 : ZMod 230653527350717) ^ (230653527350717 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 230653527350717) ^ ((230653527350717 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 230653527350717) ^ ((230653527350717 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 230653527350717) ^ ((230653527350717 - 1) / 2971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 230653527350717) ^ ((230653527350717 - 1) / 233840303) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 230653527350717 (2 : ZMod 230653527350717)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (83, 1), (2971, 1), (233840303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (83, 1), (2971, 1), (233840303, 1)] : List FactorBlock).map factorBlockValue).prod = 230653527350717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_83
      · exact prime_free64TripleA_2971
      · exact prime_free64TripleA_233840303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_1436348325469087 : Nat.Prime 1436348325469087 := by
  have hfermat : (3 : ZMod 1436348325469087) ^ (1436348325469087 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1436348325469087) ^ ((1436348325469087 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1436348325469087) ^ ((1436348325469087 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1436348325469087) ^ ((1436348325469087 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1436348325469087) ^ ((1436348325469087 - 1) / 745709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1436348325469087) ^ ((1436348325469087 - 1) / 2892119) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1436348325469087 (3 : ZMod 1436348325469087)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (37, 1), (745709, 1), (2892119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (37, 1), (745709, 1), (2892119, 1)] : List FactorBlock).map factorBlockValue).prod = 1436348325469087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_free64TripleA_745709
      · exact prime_free64TripleA_2892119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_86001505063 : Nat.Prime 86001505063 := by
  have hfermat : (3 : ZMod 86001505063) ^ (86001505063 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 86001505063) ^ ((86001505063 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 86001505063) ^ ((86001505063 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 86001505063) ^ ((86001505063 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 86001505063) ^ ((86001505063 - 1) / 1367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 86001505063) ^ ((86001505063 - 1) / 953221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 86001505063 (3 : ZMod 86001505063)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (1367, 1), (953221, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (1367, 1), (953221, 1)] : List FactorBlock).map factorBlockValue).prod = 86001505063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64TripleA_1367
      · exact prime_free64TripleA_953221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_1537706910526441 : Nat.Prime 1537706910526441 := by
  have hfermat : (11 : ZMod 1537706910526441) ^ (1537706910526441 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 1537706910526441) ^ ((1537706910526441 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 1537706910526441) ^ ((1537706910526441 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 1537706910526441) ^ ((1537706910526441 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 1537706910526441) ^ ((1537706910526441 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 1537706910526441) ^ ((1537706910526441 - 1) / 86001505063) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1537706910526441 (11 : ZMod 1537706910526441)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (149, 1), (86001505063, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (149, 1), (86001505063, 1)] : List FactorBlock).map factorBlockValue).prod = 1537706910526441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_149
      · exact prime_free64TripleA_86001505063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_4762488116064271 : Nat.Prime 4762488116064271 := by
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
      · exact prime_free64TripleA_472123
      · exact prime_free64TripleA_7819681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_9811689499 : Nat.Prime 9811689499 := by
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
      · exact prime_free64TripleA_710683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_8551005138652489 : Nat.Prime 8551005138652489 := by
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
      · exact prime_free64TripleA_36313
      · exact prime_free64TripleA_9811689499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_380330210551 : Nat.Prime 380330210551 := by
  have hfermat : (3 : ZMod 380330210551) ^ (380330210551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 380330210551) ^ ((380330210551 - 1) / 21821) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 380330210551 (3 : ZMod 380330210551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (131, 1), (887, 1), (21821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (131, 1), (887, 1), (21821, 1)] : List FactorBlock).map factorBlockValue).prod = 380330210551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64TripleA_131
      · exact prime_free64TripleA_887
      · exact prime_free64TripleA_21821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_8746834182251899 : Nat.Prime 8746834182251899 := by
  have hfermat : (3 : ZMod 8746834182251899) ^ (8746834182251899 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 8746834182251899) ^ ((8746834182251899 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 8746834182251899) ^ ((8746834182251899 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 8746834182251899) ^ ((8746834182251899 - 1) / 3833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 8746834182251899) ^ ((8746834182251899 - 1) / 380330210551) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8746834182251899 (3 : ZMod 8746834182251899)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3833, 1), (380330210551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3833, 1), (380330210551, 1)] : List FactorBlock).map factorBlockValue).prod = 8746834182251899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_3833
      · exact prime_free64TripleA_380330210551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_12144708010980709 : Nat.Prime 12144708010980709 := by
  have hfermat : (2 : ZMod 12144708010980709) ^ (12144708010980709 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12144708010980709) ^ ((12144708010980709 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12144708010980709) ^ ((12144708010980709 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12144708010980709) ^ ((12144708010980709 - 1) / 22573) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 12144708010980709) ^ ((12144708010980709 - 1) / 186799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 12144708010980709) ^ ((12144708010980709 - 1) / 240017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12144708010980709 (2 : ZMod 12144708010980709)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (22573, 1), (186799, 1), (240017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (22573, 1), (186799, 1), (240017, 1)] : List FactorBlock).map factorBlockValue).prod = 12144708010980709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_22573
      · exact prime_free64TripleA_186799
      · exact prime_free64TripleA_240017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_910838081 : Nat.Prime 910838081 := by
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
      · exact prime_free64TripleA_173
      · exact prime_free64TripleA_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_75763511577581 : Nat.Prime 75763511577581 := by
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
      · exact prime_free64TripleA_4159
      · exact prime_free64TripleA_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_17274080639688469 : Nat.Prime 17274080639688469 := by
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
      · exact prime_free64TripleA_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_27238268144131903 : Nat.Prime 27238268144131903 := by
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
      · exact prime_free64TripleA_82529
      · exact prime_free64TripleA_1244879
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

private theorem prime_free64TripleA_70858766182234507 : Nat.Prime 70858766182234507 := by
  have hfermat : (3 : ZMod 70858766182234507) ^ (70858766182234507 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 260003) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 70858766182234507) ^ ((70858766182234507 - 1) / 7076143) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 70858766182234507 (3 : ZMod 70858766182234507)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (131, 1), (260003, 1), (7076143, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (131, 1), (260003, 1), (7076143, 1)] : List FactorBlock).map factorBlockValue).prod = 70858766182234507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64TripleA_131
      · exact prime_free64TripleA_260003
      · exact prime_free64TripleA_7076143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_110295707065568641 : Nat.Prime 110295707065568641 := by
  have hfermat : (26 : ZMod 110295707065568641) ^ (110295707065568641 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 929) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (26 : ZMod 110295707065568641) ^ ((110295707065568641 - 1) / 1796567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 110295707065568641 (26 : ZMod 110295707065568641)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 2), (5, 1), (7, 1), (11, 1), (149, 1), (929, 1), (1796567, 1)] : List FactorBlock).map factorBlockValue).prod = 110295707065568641 - 1 by
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
      · exact prime_t64_149
      · exact prime_free64TripleA_929
      · exact prime_free64TripleA_1796567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7

private theorem prime_free64TripleA_14999741 : Nat.Prime 14999741 := by
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
      · exact prime_free64TripleA_5639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_11655978276633277 : Nat.Prime 11655978276633277 := by
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
      · exact prime_free64TripleA_81047
      · exact prime_free64TripleA_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_116559782766332771 : Nat.Prime 116559782766332771 := by
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
      · exact prime_free64TripleA_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_11641387 : Nat.Prime 11641387 := by
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
      · exact prime_free64TripleA_18133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_318927438253 : Nat.Prime 318927438253 := by
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
      · exact prime_free64TripleA_11641387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_157435978474087427 : Nat.Prime 157435978474087427 := by
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
      · exact prime_free64TripleA_4657
      · exact prime_free64TripleA_318927438253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_7460127281 : Nat.Prime 7460127281 := by
  have hfermat : (3 : ZMod 7460127281) ^ (7460127281 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 7460127281) ^ ((7460127281 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 7460127281) ^ ((7460127281 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 7460127281) ^ ((7460127281 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 7460127281) ^ ((7460127281 - 1) / 409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 7460127281) ^ ((7460127281 - 1) / 431) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7460127281 (3 : ZMod 7460127281)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (23, 2), (409, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (23, 2), (409, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod = 7460127281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_409
      · exact prime_t64_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_244673091811215203 : Nat.Prime 244673091811215203 := by
  have hfermat : (2 : ZMod 244673091811215203) ^ (244673091811215203 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 244673091811215203) ^ ((244673091811215203 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 244673091811215203) ^ ((244673091811215203 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 244673091811215203) ^ ((244673091811215203 - 1) / 528991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 244673091811215203) ^ ((244673091811215203 - 1) / 7460127281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 244673091811215203 (2 : ZMod 244673091811215203)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (528991, 1), (7460127281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (528991, 1), (7460127281, 1)] : List FactorBlock).map factorBlockValue).prod = 244673091811215203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64TripleA_528991
      · exact prime_free64TripleA_7460127281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_579848016567285199 : Nat.Prime 579848016567285199 := by
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
      · exact prime_free64TripleA_10531
      · exact prime_free64TripleA_418069
      · exact prime_free64TripleA_7316849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_742356388217 : Nat.Prime 742356388217 := by
  have hfermat : (3 : ZMod 742356388217) ^ (742356388217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 742356388217) ^ ((742356388217 - 1) / 4111) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 742356388217 (3 : ZMod 742356388217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (37, 1), (61, 1), (73, 1), (137, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (37, 1), (61, 1), (73, 1), (137, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod = 742356388217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_t64_61
      · exact prime_t64_73
      · exact prime_t64_137
      · exact prime_free64TripleA_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_14847127764341 : Nat.Prime 14847127764341 := by
  have hfermat : (2 : ZMod 14847127764341) ^ (14847127764341 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 14847127764341) ^ ((14847127764341 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 14847127764341) ^ ((14847127764341 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 14847127764341) ^ ((14847127764341 - 1) / 742356388217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14847127764341 (2 : ZMod 14847127764341)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (742356388217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (742356388217, 1)] : List FactorBlock).map factorBlockValue).prod = 14847127764341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64TripleA_742356388217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_125784866419496953 : Nat.Prime 125784866419496953 := by
  have hfermat : (15 : ZMod 125784866419496953) ^ (125784866419496953 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (15 : ZMod 125784866419496953) ^ ((125784866419496953 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (15 : ZMod 125784866419496953) ^ ((125784866419496953 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (15 : ZMod 125784866419496953) ^ ((125784866419496953 - 1) / 353) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (15 : ZMod 125784866419496953) ^ ((125784866419496953 - 1) / 14847127764341) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 125784866419496953 (15 : ZMod 125784866419496953)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (353, 1), (14847127764341, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (353, 1), (14847127764341, 1)] : List FactorBlock).map factorBlockValue).prod = 125784866419496953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_353
      · exact prime_free64TripleA_14847127764341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_10565928779237744053 : Nat.Prime 10565928779237744053 := by
  have hfermat : (5 : ZMod 10565928779237744053) ^ (10565928779237744053 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 10565928779237744053) ^ ((10565928779237744053 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 10565928779237744053) ^ ((10565928779237744053 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 10565928779237744053) ^ ((10565928779237744053 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 10565928779237744053) ^ ((10565928779237744053 - 1) / 125784866419496953) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10565928779237744053 (5 : ZMod 10565928779237744053)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (125784866419496953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (125784866419496953, 1)] : List FactorBlock).map factorBlockValue).prod = 10565928779237744053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64TripleA_125784866419496953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_69769875117036373 : Nat.Prime 69769875117036373 := by
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
      · exact prime_free64TripleA_2713
      · exact prime_free64TripleA_323801
      · exact prime_free64TripleA_6618487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_12000418520130256157 : Nat.Prime 12000418520130256157 := by
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
      · exact prime_free64TripleA_69769875117036373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_17628991 : Nat.Prime 17628991 := by
  have hfermat : (3 : ZMod 17628991) ^ (17628991 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 17628991) ^ ((17628991 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 17628991) ^ ((17628991 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 17628991) ^ ((17628991 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 17628991) ^ ((17628991 - 1) / 587633) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17628991 (3 : ZMod 17628991)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (587633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (587633, 1)] : List FactorBlock).map factorBlockValue).prod = 17628991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64TripleA_587633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_12164003791 : Nat.Prime 12164003791 := by
  have hfermat : (7 : ZMod 12164003791) ^ (12164003791 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 12164003791) ^ ((12164003791 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 12164003791) ^ ((12164003791 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 12164003791) ^ ((12164003791 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 12164003791) ^ ((12164003791 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 12164003791) ^ ((12164003791 - 1) / 17628991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12164003791 (7 : ZMod 12164003791)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (23, 1), (17628991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (23, 1), (17628991, 1)] : List FactorBlock).map factorBlockValue).prod = 12164003791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_free64TripleA_17628991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_222089773015888451 : Nat.Prime 222089773015888451 := by
  have hfermat : (2 : ZMod 222089773015888451) ^ (222089773015888451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 222089773015888451) ^ ((222089773015888451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 222089773015888451) ^ ((222089773015888451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 222089773015888451) ^ ((222089773015888451 - 1) / 365159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 222089773015888451) ^ ((222089773015888451 - 1) / 12164003791) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 222089773015888451 (2 : ZMod 222089773015888451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (365159, 1), (12164003791, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (365159, 1), (12164003791, 1)] : List FactorBlock).map factorBlockValue).prod = 222089773015888451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64TripleA_365159
      · exact prime_free64TripleA_12164003791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_37755261412701036671 : Nat.Prime 37755261412701036671 := by
  have hfermat : (11 : ZMod 37755261412701036671) ^ (37755261412701036671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 37755261412701036671) ^ ((37755261412701036671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 37755261412701036671) ^ ((37755261412701036671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 37755261412701036671) ^ ((37755261412701036671 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 37755261412701036671) ^ ((37755261412701036671 - 1) / 222089773015888451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 37755261412701036671 (11 : ZMod 37755261412701036671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (222089773015888451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (222089773015888451, 1)] : List FactorBlock).map factorBlockValue).prod = 37755261412701036671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_free64TripleA_222089773015888451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_28538443 : Nat.Prime 28538443 := by
  have hfermat : (3 : ZMod 28538443) ^ (28538443 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 28538443) ^ ((28538443 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 28538443) ^ ((28538443 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 28538443) ^ ((28538443 - 1) / 1585469) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28538443 (3 : ZMod 28538443)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (1585469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (1585469, 1)] : List FactorBlock).map factorBlockValue).prod = 28538443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_1585469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_17123065801 : Nat.Prime 17123065801 := by
  have hfermat : (11 : ZMod 17123065801) ^ (17123065801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 17123065801) ^ ((17123065801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 17123065801) ^ ((17123065801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 17123065801) ^ ((17123065801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 17123065801) ^ ((17123065801 - 1) / 28538443) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17123065801 (11 : ZMod 17123065801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 2), (28538443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 2), (28538443, 1)] : List FactorBlock).map factorBlockValue).prod = 17123065801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64TripleA_28538443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_105923285044987 : Nat.Prime 105923285044987 := by
  have hfermat : (2 : ZMod 105923285044987) ^ (105923285044987 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 105923285044987) ^ ((105923285044987 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 105923285044987) ^ ((105923285044987 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 105923285044987) ^ ((105923285044987 - 1) / 1031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 105923285044987) ^ ((105923285044987 - 1) / 17123065801) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 105923285044987 (2 : ZMod 105923285044987)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1031, 1), (17123065801, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1031, 1), (17123065801, 1)] : List FactorBlock).map factorBlockValue).prod = 105923285044987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_1031
      · exact prime_free64TripleA_17123065801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_66686546258912645539 : Nat.Prime 66686546258912645539 := by
  have hfermat : (2 : ZMod 66686546258912645539) ^ (66686546258912645539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 66686546258912645539) ^ ((66686546258912645539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 66686546258912645539) ^ ((66686546258912645539 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 66686546258912645539) ^ ((66686546258912645539 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 66686546258912645539) ^ ((66686546258912645539 - 1) / 9539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 66686546258912645539) ^ ((66686546258912645539 - 1) / 105923285044987) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 66686546258912645539 (2 : ZMod 66686546258912645539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (9539, 1), (105923285044987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (9539, 1), (105923285044987, 1)] : List FactorBlock).map factorBlockValue).prod = 66686546258912645539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64TripleA_9539
      · exact prime_free64TripleA_105923285044987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_19817141 : Nat.Prime 19817141 := by
  have hfermat : (3 : ZMod 19817141) ^ (19817141 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 19817141) ^ ((19817141 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 19817141) ^ ((19817141 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 19817141) ^ ((19817141 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 19817141) ^ ((19817141 - 1) / 141551) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19817141 (3 : ZMod 19817141)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7, 1), (141551, 1)] : List FactorBlock).map factorBlockValue).prod = 19817141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64TripleA_141551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_3285231637 : Nat.Prime 3285231637 := by
  have hfermat : (2 : ZMod 3285231637) ^ (3285231637 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3285231637) ^ ((3285231637 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3285231637) ^ ((3285231637 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3285231637) ^ ((3285231637 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3285231637) ^ ((3285231637 - 1) / 4086109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3285231637 (2 : ZMod 3285231637)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (67, 1), (4086109, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (67, 1), (4086109, 1)] : List FactorBlock).map factorBlockValue).prod = 3285231637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_free64TripleA_4086109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_85676730515606199173 : Nat.Prime 85676730515606199173 := by
  have hfermat : (2 : ZMod 85676730515606199173) ^ (85676730515606199173 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 85676730515606199173) ^ ((85676730515606199173 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 85676730515606199173) ^ ((85676730515606199173 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 85676730515606199173) ^ ((85676730515606199173 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 85676730515606199173) ^ ((85676730515606199173 - 1) / 19817141) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 85676730515606199173) ^ ((85676730515606199173 - 1) / 3285231637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 85676730515606199173 (2 : ZMod 85676730515606199173)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (47, 1), (19817141, 1), (3285231637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (47, 1), (19817141, 1), (3285231637, 1)] : List FactorBlock).map factorBlockValue).prod = 85676730515606199173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_free64TripleA_19817141
      · exact prime_free64TripleA_3285231637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_14615833261 : Nat.Prime 14615833261 := by
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
      · exact prime_free64TripleA_181
      · exact prime_free64TripleA_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_175389999133 : Nat.Prime 175389999133 := by
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
      · exact prime_free64TripleA_14615833261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_1052339994799 : Nat.Prime 1052339994799 := by
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
      · exact prime_free64TripleA_175389999133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_138104211745804923847 : Nat.Prime 138104211745804923847 := by
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
      · exact prime_free64TripleA_7290853
      · exact prime_free64TripleA_1052339994799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_4153387267 : Nat.Prime 4153387267 := by
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
      · exact prime_free64TripleA_215447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_15272295717867691 : Nat.Prime 15272295717867691 := by
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
      · exact prime_free64TripleA_6451
      · exact prime_free64TripleA_4153387267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_1366687199200543932209 : Nat.Prime 1366687199200543932209 := by
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
      · exact prime_free64TripleA_15272295717867691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_19518469961 : Nat.Prime 19518469961 := by
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
      · exact prime_free64TripleA_561521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_44650621068881221949 : Nat.Prime 44650621068881221949 := by
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
      · exact prime_free64TripleA_2161
      · exact prime_free64TripleA_8537
      · exact prime_free64TripleA_19518469961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_1964627327030773765757 : Nat.Prime 1964627327030773765757 := by
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
      · exact prime_free64TripleA_44650621068881221949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_7240757107 : Nat.Prime 7240757107 := by
  have hfermat : (2 : ZMod 7240757107) ^ (7240757107 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7240757107) ^ ((7240757107 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7240757107) ^ ((7240757107 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7240757107) ^ ((7240757107 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7240757107) ^ ((7240757107 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 7240757107) ^ ((7240757107 - 1) / 2965093) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7240757107 (2 : ZMod 7240757107)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (37, 1), (2965093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (37, 1), (2965093, 1)] : List FactorBlock).map factorBlockValue).prod = 7240757107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_37
      · exact prime_free64TripleA_2965093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_8211018559339 : Nat.Prime 8211018559339 := by
  have hfermat : (2 : ZMod 8211018559339) ^ (8211018559339 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 8211018559339) ^ ((8211018559339 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 8211018559339) ^ ((8211018559339 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 8211018559339) ^ ((8211018559339 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 8211018559339) ^ ((8211018559339 - 1) / 7240757107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8211018559339 (2 : ZMod 8211018559339)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (7, 1), (7240757107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (7, 1), (7240757107, 1)] : List FactorBlock).map factorBlockValue).prod = 8211018559339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64TripleA_7240757107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_29320883332438860848461 : Nat.Prime 29320883332438860848461 := by
  have hfermat : (6 : ZMod 29320883332438860848461) ^ (29320883332438860848461 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 5501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (6 : ZMod 29320883332438860848461) ^ ((29320883332438860848461 - 1) / 8211018559339) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 29320883332438860848461 (6 : ZMod 29320883332438860848461)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (31, 1), (349, 1), (5501, 1), (8211018559339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (31, 1), (349, 1), (5501, 1), (8211018559339, 1)] : List FactorBlock).map factorBlockValue).prod = 29320883332438860848461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_t64_349
      · exact prime_free64TripleA_5501
      · exact prime_free64TripleA_8211018559339
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

private theorem prime_free64TripleA_5319909443 : Nat.Prime 5319909443 := by
  have hfermat : (2 : ZMod 5319909443) ^ (5319909443 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5319909443) ^ ((5319909443 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5319909443) ^ ((5319909443 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5319909443) ^ ((5319909443 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5319909443) ^ ((5319909443 - 1) / 1208521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5319909443 (2 : ZMod 5319909443)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (71, 1), (1208521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (71, 1), (1208521, 1)] : List FactorBlock).map factorBlockValue).prod = 5319909443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_71
      · exact prime_free64TripleA_1208521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_746149218837409 : Nat.Prime 746149218837409 := by
  have hfermat : (29 : ZMod 746149218837409) ^ (746149218837409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (29 : ZMod 746149218837409) ^ ((746149218837409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (29 : ZMod 746149218837409) ^ ((746149218837409 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (29 : ZMod 746149218837409) ^ ((746149218837409 - 1) / 487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (29 : ZMod 746149218837409) ^ ((746149218837409 - 1) / 5319909443) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 746149218837409 (29 : ZMod 746149218837409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (487, 1), (5319909443, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (487, 1), (5319909443, 1)] : List FactorBlock).map factorBlockValue).prod = 746149218837409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_487
      · exact prime_free64TripleA_5319909443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_22384476565122271 : Nat.Prime 22384476565122271 := by
  have hfermat : (15 : ZMod 22384476565122271) ^ (22384476565122271 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (15 : ZMod 22384476565122271) ^ ((22384476565122271 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (15 : ZMod 22384476565122271) ^ ((22384476565122271 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (15 : ZMod 22384476565122271) ^ ((22384476565122271 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (15 : ZMod 22384476565122271) ^ ((22384476565122271 - 1) / 746149218837409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 22384476565122271 (15 : ZMod 22384476565122271)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (746149218837409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (746149218837409, 1)] : List FactorBlock).map factorBlockValue).prod = 22384476565122271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64TripleA_746149218837409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_61277459828069086617959 : Nat.Prime 61277459828069086617959 := by
  have hfermat : (11 : ZMod 61277459828069086617959) ^ (61277459828069086617959 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 61277459828069086617959) ^ ((61277459828069086617959 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 61277459828069086617959) ^ ((61277459828069086617959 - 1) / 313) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 61277459828069086617959) ^ ((61277459828069086617959 - 1) / 4373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 61277459828069086617959) ^ ((61277459828069086617959 - 1) / 22384476565122271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 61277459828069086617959 (11 : ZMod 61277459828069086617959)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (313, 1), (4373, 1), (22384476565122271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (313, 1), (4373, 1), (22384476565122271, 1)] : List FactorBlock).map factorBlockValue).prod = 61277459828069086617959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64TripleA_313
      · exact prime_free64TripleA_4373
      · exact prime_free64TripleA_22384476565122271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_4696532563 : Nat.Prime 4696532563 := by
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
      · exact prime_free64TripleA_3823
      · exact prime_free64TripleA_204749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_7776862710917 : Nat.Prime 7776862710917 := by
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
      · exact prime_free64TripleA_1933
      · exact prime_free64TripleA_3363887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_73048577919604292180543 : Nat.Prime 73048577919604292180543 := by
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
      · exact prime_free64TripleA_4696532563
      · exact prime_free64TripleA_7776862710917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_2342693833 : Nat.Prime 2342693833 := by
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
      · exact prime_free64TripleA_150869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_629210080442473 : Nat.Prime 629210080442473 := by
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
      · exact prime_free64TripleA_2342693833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_3775260482654839 : Nat.Prime 3775260482654839 := by
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
      · exact prime_free64TripleA_629210080442473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_73681381313926227279101 : Nat.Prime 73681381313926227279101 := by
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
      · exact prime_free64TripleA_15013
      · exact prime_free64TripleA_3775260482654839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_195459090284826782901691 : Nat.Prime 195459090284826782901691 := by
  have hfermat : (2 : ZMod 195459090284826782901691) ^ (195459090284826782901691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 15493) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 20929) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 1262869) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (2 : ZMod 195459090284826782901691) ^ ((195459090284826782901691 - 1) / 2272973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 195459090284826782901691 (2 : ZMod 195459090284826782901691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (15493, 1), (20929, 1), (1262869, 1), (2272973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (15493, 1), (20929, 1), (1262869, 1), (2272973, 1)] : List FactorBlock).map factorBlockValue).prod = 195459090284826782901691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64TripleA_15493
      · exact prime_free64TripleA_20929
      · exact prime_free64TripleA_1262869
      · exact prime_free64TripleA_2272973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5
    · exact hfactor_6
    · exact hfactor_7

private theorem prime_free64TripleA_17224505407 : Nat.Prime 17224505407 := by
  have hfermat : (5 : ZMod 17224505407) ^ (17224505407 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 17224505407) ^ ((17224505407 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 17224505407) ^ ((17224505407 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 17224505407) ^ ((17224505407 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 17224505407) ^ ((17224505407 - 1) / 193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 17224505407) ^ ((17224505407 - 1) / 62761) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17224505407 (5 : ZMod 17224505407)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (79, 1), (193, 1), (62761, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (79, 1), (193, 1), (62761, 1)] : List FactorBlock).map factorBlockValue).prod = 17224505407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_79
      · exact prime_t64_193
      · exact prime_free64TripleA_62761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_12560074893773587 : Nat.Prime 12560074893773587 := by
  have hfermat : (2 : ZMod 12560074893773587) ^ (12560074893773587 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12560074893773587) ^ ((12560074893773587 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12560074893773587) ^ ((12560074893773587 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12560074893773587) ^ ((12560074893773587 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 12560074893773587) ^ ((12560074893773587 - 1) / 2383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 12560074893773587) ^ ((12560074893773587 - 1) / 17224505407) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12560074893773587 (2 : ZMod 12560074893773587)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (17, 1), (2383, 1), (17224505407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (17, 1), (2383, 1), (17224505407, 1)] : List FactorBlock).map factorBlockValue).prod = 12560074893773587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_free64TripleA_2383
      · exact prime_free64TripleA_17224505407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_751918730614472504247209 : Nat.Prime 751918730614472504247209 := by
  have hfermat : (3 : ZMod 751918730614472504247209) ^ (751918730614472504247209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 751918730614472504247209) ^ ((751918730614472504247209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 751918730614472504247209) ^ ((751918730614472504247209 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 751918730614472504247209) ^ ((751918730614472504247209 - 1) / 680293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 751918730614472504247209) ^ ((751918730614472504247209 - 1) / 12560074893773587) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 751918730614472504247209 (3 : ZMod 751918730614472504247209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (680293, 1), (12560074893773587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (680293, 1), (12560074893773587, 1)] : List FactorBlock).map factorBlockValue).prod = 751918730614472504247209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64TripleA_680293
      · exact prime_free64TripleA_12560074893773587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_3803035501 : Nat.Prime 3803035501 := by
  have hfermat : (2 : ZMod 3803035501) ^ (3803035501 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3803035501) ^ ((3803035501 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3803035501) ^ ((3803035501 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3803035501) ^ ((3803035501 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3803035501) ^ ((3803035501 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 3803035501) ^ ((3803035501 - 1) / 76829) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3803035501 (2 : ZMod 3803035501)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 3), (11, 1), (76829, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 3), (11, 1), (76829, 1)] : List FactorBlock).map factorBlockValue).prod = 3803035501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64TripleA_76829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_106484994029 : Nat.Prime 106484994029 := by
  have hfermat : (3 : ZMod 106484994029) ^ (106484994029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 106484994029) ^ ((106484994029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 106484994029) ^ ((106484994029 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 106484994029) ^ ((106484994029 - 1) / 3803035501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 106484994029 (3 : ZMod 106484994029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (3803035501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (3803035501, 1)] : List FactorBlock).map factorBlockValue).prod = 106484994029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64TripleA_3803035501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_143898111502290928372853 : Nat.Prime 143898111502290928372853 := by
  have hfermat : (2 : ZMod 143898111502290928372853) ^ (143898111502290928372853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 143898111502290928372853) ^ ((143898111502290928372853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 143898111502290928372853) ^ ((143898111502290928372853 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 143898111502290928372853) ^ ((143898111502290928372853 - 1) / 4229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 143898111502290928372853) ^ ((143898111502290928372853 - 1) / 3473291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 143898111502290928372853) ^ ((143898111502290928372853 - 1) / 106484994029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 143898111502290928372853 (2 : ZMod 143898111502290928372853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (23, 1), (4229, 1), (3473291, 1), (106484994029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (23, 1), (4229, 1), (3473291, 1), (106484994029, 1)] : List FactorBlock).map factorBlockValue).prod = 143898111502290928372853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_free64TripleA_4229
      · exact prime_free64TripleA_3473291
      · exact prime_free64TripleA_106484994029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64TripleA_863388669013745570237119 : Nat.Prime 863388669013745570237119 := by
  have hfermat : (3 : ZMod 863388669013745570237119) ^ (863388669013745570237119 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 863388669013745570237119) ^ ((863388669013745570237119 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 863388669013745570237119) ^ ((863388669013745570237119 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 863388669013745570237119) ^ ((863388669013745570237119 - 1) / 143898111502290928372853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 863388669013745570237119 (3 : ZMod 863388669013745570237119)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (143898111502290928372853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (143898111502290928372853, 1)] : List FactorBlock).map factorBlockValue).prod = 863388669013745570237119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64TripleA_143898111502290928372853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_71315977 : Nat.Prime 71315977 := by
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
      · exact prime_free64TripleA_2971499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64TripleA_14671693316257 : Nat.Prime 14671693316257 := by
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
      · exact prime_free64TripleA_2143
      · exact prime_free64TripleA_71315977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64TripleA_1142654849326181315249383 : Nat.Prime 1142654849326181315249383 := by
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
      · exact prime_free64TripleA_769
      · exact prime_free64TripleA_1523
      · exact prime_free64TripleA_11083
      · exact prime_free64TripleA_14671693316257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64TripleA_41727066497746668265106881 : Nat.Prime 41727066497746668265106881 := by
  have hfermat : (17 : ZMod 41727066497746668265106881) ^ (41727066497746668265106881 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (17 : ZMod 41727066497746668265106881) ^ ((41727066497746668265106881 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 41727066497746668265106881 (17 : ZMod 41727066497746668265106881)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 4), (5, 1), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 41727066497746668265106881 - 1 by
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

private theorem prime_free64TripleA_47929738544709010845055201 : Nat.Prime 47929738544709010845055201 := by
  have hfermat : (71 : ZMod 47929738544709010845055201) ^ (47929738544709010845055201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (71 : ZMod 47929738544709010845055201) ^ ((47929738544709010845055201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 47929738544709010845055201 (71 : ZMod 47929738544709010845055201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 47929738544709010845055201 - 1 by
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

private theorem prime_free64TripleA_77104362006705800055088801 : Nat.Prime 77104362006705800055088801 := by
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

private theorem prime_free64TripleA_88670016307711670063352121 : Nat.Prime 88670016307711670063352121 := by
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

private theorem prime_free64TripleA_126671451868159528661931601 : Nat.Prime 126671451868159528661931601 := by
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

private theorem prime_free64TripleA_141872026092338672101363393 : Nat.Prime 141872026092338672101363393 := by
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

private theorem prime_free64TripleA_208635332488733341325534401 : Nat.Prime 208635332488733341325534401 := by
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

private theorem prime_free64TripleA_272830819408343600194929601 : Nat.Prime 272830819408343600194929601 := by
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

private theorem prime_free64TripleA_3546800652308466802534084883 : Nat.Prime 3546800652308466802534084883 := by
  have hfermat : (2 : ZMod 3546800652308466802534084883) ^ (3546800652308466802534084883 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3546800652308466802534084883) ^ ((3546800652308466802534084883 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3546800652308466802534084883) ^ ((3546800652308466802534084883 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3546800652308466802534084883) ^ ((3546800652308466802534084883 - 1) / 3561523789) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3546800652308466802534084883) ^ ((3546800652308466802534084883 - 1) / 12144708010980709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3546800652308466802534084883 (2 : ZMod 3546800652308466802534084883)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (3561523789, 1), (12144708010980709, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (3561523789, 1), (12144708010980709, 1)] : List FactorBlock).map factorBlockValue).prod = 3546800652308466802534084883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_free64TripleA_3561523789
      · exact prime_free64TripleA_12144708010980709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem phi_free64TripleA_3546800652308466802534084797 :
    Nat.totient 3546800652308466802534084797 = 2345914417695629553539117568 := by
  rw [← show
    ((([(3, 1), (127, 1), (4597709, 1), (5054317, 1), (400597142329, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084797 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64TripleA_127, prime_free64TripleA_4597709, prime_free64TripleA_5054317, prime_free64TripleA_400597142329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084798 :
    Nat.totient 3546800652308466802534084798 = 1763493061488597332733124800 := by
  rw [← show
    ((([(2, 1), (179, 1), (6442882141, 1), (1537706910526441, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084798 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_179, prime_free64TripleA_6442882141, prime_free64TripleA_1537706910526441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084799 :
    Nat.totient 3546800652308466802534084799 = 3545896115560386435976719360 := by
  rw [← show
    ((([(3923, 1), (8197093, 1), (110295707065568641, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084799 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_3923, prime_free64TripleA_8197093, prime_free64TripleA_110295707065568641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084800 :
    Nat.totient 3546800652308466802534084800 = 466714105378081918156800000 := by
  rw [← show
    ((([(2, 6), (3, 4), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084800 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084801 :
    Nat.totient 3546800652308466802534084801 = 3546800652191906989338726100 := by
  rw [← show
    ((([(30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084801 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_30429025931, prime_free64TripleA_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084802 :
    Nat.totient 3546800652308466802534084802 = 1773165808697241942288587520 := by
  rw [← show
    ((([(2, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084802 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64TripleA_8233, prime_free64TripleA_93811, prime_free64TripleA_8274073, prime_free64TripleA_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084803 :
    Nat.totient 3546800652308466802534084803 = 2341109655706591279001952384 := by
  rw [← show
    ((([(3, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084803 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084804 :
    Nat.totient 3546800652308466802534084804 = 1770061660403267701267660800 := by
  rw [← show
    ((([(2, 2), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084804 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64TripleA_769, prime_free64TripleA_2143, prime_free64TripleA_8597, prime_free64TripleA_9792301, prime_free64TripleA_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084805 :
    Nat.totient 3546800652308466802534084805 = 2823516964197063832352578560 := by
  rw [← show
    ((([(5, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084805 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64TripleA_281, prime_free64TripleA_739, prime_free64TripleA_3540386347, prime_free64TripleA_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084806 :
    Nat.totient 3546800652308466802534084806 = 1182266883135824490764412200 := by
  rw [← show
    ((([(2, 1), (3, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084806 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084807 :
    Nat.totient 3546800652308466802534084807 = 3035933043531011885696786208 := by
  rw [← show
    ((([(7, 1), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084807 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64TripleA_727, prime_free64TripleA_40346827, prime_free64TripleA_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084808 :
    Nat.totient 3546800652308466802534084808 = 1768600357161504794147819520 := by
  rw [← show
    ((([(2, 3), (373, 1), (55249, 1), (157429, 1), (773027, 1), (176780411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084808 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64TripleA_373, prime_free64TripleA_55249, prime_free64TripleA_157429, prime_free64TripleA_773027, prime_free64TripleA_176780411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084809 :
    Nat.totient 3546800652308466802534084809 = 2364533768205644535022723200 := by
  rw [← show
    ((([(3, 2), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084809 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084810 :
    Nat.totient 3546800652308466802534084810 = 1418712402414078597917848768 := by
  rw [← show
    ((([(2, 1), (5, 1), (180533, 1), (1964627327030773765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084810 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64TripleA_180533, prime_free64TripleA_1964627327030773765757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084811 :
    Nat.totient 3546800652308466802534084811 = 3223668872151569955168257280 := by
  rw [← show
    ((([(11, 1), (4637, 1), (2076644077, 1), (33484585780649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084811 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_free64TripleA_4637, prime_free64TripleA_2076644077, prime_free64TripleA_33484585780649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084812 :
    Nat.totient 3546800652308466802534084812 = 1182266827618099149325191168 := by
  rw [← show
    ((([(2, 2), (3, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084812 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084813 :
    Nat.totient 3546800652308466802534084813 = 3273969832900123202339155200 := by
  rw [← show
    ((([(13, 1), (272830819408343600194929601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084813 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_free64TripleA_272830819408343600194929601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084814 :
    Nat.totient 3546800652308466802534084814 = 1520049639025954634725411200 := by
  rw [← show
    ((([(2, 1), (7, 1), (339389, 1), (545911, 1), (2940799, 1), (464968781, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084814 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64TripleA_339389, prime_free64TripleA_545911, prime_free64TripleA_2940799, prime_free64TripleA_464968781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084815 :
    Nat.totient 3546800652308466802534084815 = 1891627011543136663647837216 := by
  rw [← show
    ((([(3, 1), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084815 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084816 :
    Nat.totient 3546800652308466802534084816 = 1757876067636611528762956800 := by
  rw [← show
    ((([(2, 4), (197, 1), (271, 1), (152441, 1), (27238268144131903, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084816 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_197, prime_free64TripleA_271, prime_free64TripleA_152441, prime_free64TripleA_27238268144131903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084817 :
    Nat.totient 3546800652308466802534084817 = 3338165319819733461208550400 := by
  rw [← show
    ((([(17, 1), (208635332488733341325534401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084817 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_free64TripleA_208635332488733341325534401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084818 :
    Nat.totient 3546800652308466802534084818 = 1179350121420745283582330688 := by
  rw [← show
    ((([(2, 1), (3, 2), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084818 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084819 :
    Nat.totient 3546800652308466802534084819 = 3360126923328651614184211272 := by
  rw [← show
    ((([(19, 1), (321935599, 1), (579848016567285199, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084819 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_free64TripleA_321935599, prime_free64TripleA_579848016567285199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084820 :
    Nat.totient 3546800652308466802534084820 = 1409511472084176448681309824 := by
  rw [← show
    ((([(2, 2), (5, 1), (157, 1), (8179, 1), (138104211745804923847, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084820 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_157, prime_free64TripleA_8179, prime_free64TripleA_138104211745804923847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084821 :
    Nat.totient 3546800652308466802534084821 = 2022346823602002270213839040 := by
  rw [← show
    ((([(3, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084821 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084822 :
    Nat.totient 3546800652308466802534084822 = 1611451628906470685502756520 := by
  rw [← show
    ((([(2, 1), (11, 1), (2207, 1), (73048577919604292180543, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084822 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64TripleA_2207, prime_free64TripleA_73048577919604292180543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084823 :
    Nat.totient 3546800652308466802534084823 = 3392591924831463654444958264 := by
  rw [← show
    ((([(23, 1), (979501163, 1), (157435978474087427, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084823 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_free64TripleA_979501163, prime_free64TripleA_157435978474087427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084824 :
    Nat.totient 3546800652308466802534084824 = 1176077000958651971838301440 := by
  rw [← show
    ((([(2, 3), (3, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084824 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084825 :
    Nat.totient 3546800652308466802534084825 = 2837440521846773442027267840 := by
  rw [← show
    ((([(5, 2), (141872026092338672101363393, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084825 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64TripleA_141872026092338672101363393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084826 :
    Nat.totient 3546800652308466802534084826 = 1632347565246685576242455040 := by
  rw [← show
    ((([(2, 1), (13, 1), (353, 1), (9879116647, 1), (39117456919511, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084826 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_free64TripleA_353, prime_free64TripleA_9879116647, prime_free64TripleA_39117456919511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084827 :
    Nat.totient 3546800652308466802534084827 = 2364533768205644535022723200 := by
  rw [← show
    ((([(3, 3), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084827 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084828 :
    Nat.totient 3546800652308466802534084828 = 1520057422417914343943179200 := by
  rw [← show
    ((([(2, 2), (7, 1), (126671451868159528661931601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084828 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64TripleA_126671451868159528661931601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084829 :
    Nat.totient 3546800652308466802534084829 = 3388946914113604777817533440 := by
  rw [← show
    ((([(29, 1), (109, 1), (821, 1), (1366687199200543932209, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084829 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_t64_109, prime_free64TripleA_821, prime_free64TripleA_1366687199200543932209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084830 :
    Nat.totient 3546800652308466802534084830 = 936449017111146350504048000 := by
  rw [← show
    ((([(2, 1), (3, 1), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084830 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084831 :
    Nat.totient 3546800652308466802534084831 = 3360802780989327324598272000 := by
  rw [← show
    ((([(31, 1), (73, 1), (193, 1), (811, 1), (1171, 1), (8551005138652489, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084831 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_t64_73, prime_t64_193, prime_free64TripleA_811, prime_free64TripleA_1171, prime_free64TripleA_8551005138652489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084832 :
    Nat.totient 3546800652308466802534084832 = 1755117848565014500223050752 := by
  rw [← show
    ((([(2, 5), (97, 1), (1142654849326181315249383, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084832 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_97, prime_free64TripleA_1142654849326181315249383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084833 :
    Nat.totient 3546800652308466802534084833 = 2149576152914222304566112000 := by
  rw [← show
    ((([(3, 1), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084833 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084834 :
    Nat.totient 3546800652308466802534084834 = 1669081902800936476398594048 := by
  rw [← show
    ((([(2, 1), (17, 1), (2217799, 1), (370033847, 1), (127114246817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084834 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64TripleA_2217799, prime_free64TripleA_370033847, prime_free64TripleA_127114246817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084835 :
    Nat.totient 3546800652308466802534084835 = 2396459925868615180995133440 := by
  rw [← show
    ((([(5, 1), (7, 1), (71, 1), (2549, 1), (6113, 1), (54049, 1), (1694722097147, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084835 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_t64_71, prime_free64TripleA_2549, prime_free64TripleA_6113, prime_free64TripleA_54049, prime_free64TripleA_1694722097147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084836 :
    Nat.totient 3546800652308466802534084836 = 1178464326371685028751178240 := by
  rw [← show
    ((([(2, 2), (3, 2), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084836 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_311, prime_t64_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084837 :
    Nat.totient 3546800652308466802534084837 = 3448288645491747436661880000 := by
  rw [← show
    ((([(37, 1), (1301, 1), (73681381313926227279101, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084837 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_free64TripleA_1301, prime_free64TripleA_73681381313926227279101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084838 :
    Nat.totient 3546800652308466802534084838 = 1655843182574927956503304320 := by
  rw [← show
    ((([(2, 1), (19, 1), (83, 1), (733, 1), (967, 1), (171370811, 1), (9257799907, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084838 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_83, prime_free64TripleA_733, prime_free64TripleA_967, prime_free64TripleA_171370811, prime_free64TripleA_9257799907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084839 :
    Nat.totient 3546800652308466802534084839 = 2182644900860521172980664448 := by
  rw [← show
    ((([(3, 1), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084839 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_t64_1319293, prime_lucas_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084840 :
    Nat.totient 3546800652308466802534084840 = 1418720260923386721013633920 := by
  rw [← show
    ((([(2, 3), (5, 1), (88670016307711670063352121, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084840 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64TripleA_88670016307711670063352121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084841 :
    Nat.totient 3546800652308466802534084841 = 3460292839308592660388318080 := by
  rw [← show
    ((([(41, 1), (7208693, 1), (12000418520130256157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084841 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_free64TripleA_7208693, prime_free64TripleA_12000418520130256157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084842 :
    Nat.totient 3546800652308466802534084842 = 1009659458204822863872000000 := by
  rw [← show
    ((([(2, 1), (3, 1), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084842 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_433, prime_t64_751, prime_t64_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084843 :
    Nat.totient 3546800652308466802534084843 = 3464121860416977850674017280 := by
  rw [← show
    ((([(43, 1), (17761, 1), (891929189, 1), (5206795646669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084843 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_free64TripleA_17761, prime_free64TripleA_891929189, prime_free64TripleA_5206795646669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084844 :
    Nat.totient 3546800652308466802534084844 = 1612182114684215645623200000 := by
  rw [← show
    ((([(2, 2), (11, 1), (1128574980601, 1), (71425565088601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084844 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64TripleA_1128574980601, prime_free64TripleA_71425565088601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084845 :
    Nat.totient 3546800652308466802534084845 = 1891626654257559177342033888 := by
  rw [← show
    ((([(3, 2), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084845 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_5250043, prime_lucas_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084846 :
    Nat.totient 3546800652308466802534084846 = 1696295964147527601211953600 := by
  rw [← show
    ((([(2, 1), (23, 1), (77104362006705800055088801, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084846 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_free64TripleA_77104362006705800055088801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084847 :
    Nat.totient 3546800652308466802534084847 = 3419525797039499211249150240 := by
  rw [← show
    ((([(47, 1), (67, 1), (236499493, 1), (4762488116064271, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084847 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_67, prime_free64TripleA_236499493, prime_free64TripleA_4762488116064271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084848 :
    Nat.totient 3546800652308466802534084848 = 1182266884096899802201308672 := by
  rw [← show
    ((([(2, 4), (3, 1), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084848 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084849 :
    Nat.totient 3546800652308466802534084849 = 3027500258937767699853312000 := by
  rw [← show
    ((([(7, 2), (241, 1), (2046113681, 1), (146789130460481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084849 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64TripleA_241, prime_free64TripleA_2046113681, prime_free64TripleA_146789130460481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084850 :
    Nat.totient 3546800652308466802534084850 = 1412858513507228299449569280 := by
  rw [← show
    ((([(2, 1), (5, 2), (257, 1), (4139, 1), (66686546258912645539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084850 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64TripleA_257, prime_free64TripleA_4139, prime_free64TripleA_66686546258912645539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084851 :
    Nat.totient 3546800652308466802534084851 = 2225443546546488974139033600 := by
  rw [← show
    ((([(3, 1), (17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084851 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_lucas_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084852 :
    Nat.totient 3546800652308466802534084852 = 1616263588393731707483884896 := by
  rw [← show
    ((([(2, 2), (13, 1), (79, 1), (863388669013745570237119, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084852 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_79, prime_free64TripleA_863388669013745570237119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084853 :
    Nat.totient 3546800652308466802534084853 = 3440780111291826179435223808 := by
  rw [← show
    ((([(53, 1), (89, 1), (751918730614472504247209, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084853 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_t64_89, prime_free64TripleA_751918730614472504247209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084854 :
    Nat.totient 3546800652308466802534084854 = 1180116012293050661756928000 := by
  rw [← show
    ((([(2, 1), (3, 3), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084854 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_1051, prime_t64_1153, prime_t64_940369, prime_t64_6947861, prime_t64_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084855 :
    Nat.totient 3546800652308466802534084855 = 2577840209961215257903057920 := by
  rw [← show
    ((([(5, 1), (11, 1), (1787, 1), (12799, 1), (411013, 1), (6859902452969, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084855 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_free64TripleA_1787, prime_free64TripleA_12799, prime_free64TripleA_411013, prime_free64TripleA_6859902452969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084856 :
    Nat.totient 3546800652308466802534084856 = 1520049621760695199564790400 := by
  rw [← show
    ((([(2, 3), (7, 1), (194867, 1), (15463617703, 1), (21018385301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084856 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64TripleA_194867, prime_free64TripleA_15463617703, prime_free64TripleA_21018385301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084857 :
    Nat.totient 3546800652308466802534084857 = 2237238263396874131044008912 := by
  rw [← show
    ((([(3, 1), (19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084857 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_t64_787, prime_lucas_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084858 :
    Nat.totient 3546800652308466802534084858 = 1712248470065267109655134336 := by
  rw [← show
    ((([(2, 1), (29, 1), (15295123, 1), (197435923, 1), (20250214969, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084858 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_free64TripleA_15295123, prime_free64TripleA_197435923, prime_free64TripleA_20250214969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084859 :
    Nat.totient 3546800652308466802534084859 = 3486685372824063619122472456 := by
  rw [← show
    ((([(59, 1), (245696267, 1), (244673091811215203, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084859 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_free64TripleA_245696267, prime_free64TripleA_244673091811215203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084860 :
    Nat.totient 3546800652308466802534084860 = 938909759053920165731648512 := by
  rw [← show
    ((([(2, 2), (3, 1), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084860 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_137, prime_lucas_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084861 :
    Nat.totient 3546800652308466802534084861 = 3488654114004118650174006000 := by
  rw [← show
    ((([(61, 1), (1540031, 1), (37755261412701036671, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084861 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_free64TripleA_1540031, prime_free64TripleA_37755261412701036671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084862 :
    Nat.totient 3546800652308466802534084862 = 1716193863757820650518924120 := by
  rw [← show
    ((([(2, 1), (31, 1), (6540247699, 1), (8746834182251899, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084862 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_free64TripleA_6540247699, prime_free64TripleA_8746834182251899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084863 :
    Nat.totient 3546800652308466802534084863 = 2023610705578511419242210192 := by
  rw [← show
    ((([(3, 2), (7, 1), (647, 1), (87014564223362204129783, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084863 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_647, prime_lucas_87014564223362204129783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084864 :
    Nat.totient 3546800652308466802534084864 = 1769873368358692973145415680 := by
  rw [← show
    ((([(2, 8), (503, 1), (2424967, 1), (3047861, 1), (3726729229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084864 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64TripleA_503, prime_free64TripleA_2424967, prime_free64TripleA_3047861, prime_free64TripleA_3726729229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084865 :
    Nat.totient 3546800652308466802534084865 = 2617768463920141496550508800 := by
  rw [← show
    ((([(5, 1), (13, 1), (1861, 1), (29320883332438860848461, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084865 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_free64TripleA_1861, prime_free64TripleA_29320883332438860848461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084866 :
    Nat.totient 3546800652308466802534084866 = 1074771630455103695420275200 := by
  rw [← show
    ((([(2, 1), (3, 1), (11, 1), (65353, 1), (10672982981, 1), (77044474757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084866 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_65353, prime_lucas_10672982981, prime_lucas_77044474757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084867 :
    Nat.totient 3546800652308466802534084867 = 3539788954359800106758650080 := by
  rw [← show
    ((([(509, 1), (81331, 1), (85676730515606199173, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084867 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_509, prime_free64TripleA_81331, prime_free64TripleA_85676730515606199173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084868 :
    Nat.totient 3546800652308466802534084868 = 1669082255301780521057197056 := by
  rw [← show
    ((([(2, 2), (17, 1), (4138139, 1), (1577934587, 1), (7987921657, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084868 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64TripleA_4138139, prime_free64TripleA_1577934587, prime_free64TripleA_7987921657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084869 :
    Nat.totient 3546800652308466802534084869 = 2261441693754456068779880000 := by
  rw [← show
    ((([(3, 1), (23, 1), (7901, 1), (6505873687440897781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084869 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_t64_7901, prime_lucas_6505873687440897781301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084870 :
    Nat.totient 3546800652308466802534084870 = 1215973322386815293436500352 := by
  rw [← show
    ((([(2, 1), (5, 1), (7, 1), (16747, 1), (436680877, 1), (6928473265039, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084870 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_free64TripleA_16747, prime_free64TripleA_436680877, prime_free64TripleA_6928473265039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084871 :
    Nat.totient 3546800652308466802534084871 = 3544767424505362767193497600 := by
  rw [← show
    ((([(2081, 1), (12113, 1), (97961, 1), (1436348325469087, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084871 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_2081, prime_free64TripleA_12113, prime_free64TripleA_97961, prime_free64TripleA_1436348325469087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084872 :
    Nat.totient 3546800652308466802534084872 = 1171529982311936482946511360 := by
  rw [← show
    ((([(2, 3), (3, 2), (113, 1), (4271, 1), (102069566040058032487, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084872 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_113, prime_t64_4271, prime_lucas_102069566040058032487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084873 :
    Nat.totient 3546800652308466802534084873 = 3546775844034100257964191120 := by
  rw [← show
    ((([(143159, 1), (107413291, 1), (230653527350717, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084873 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_143159, prime_free64TripleA_107413291, prime_free64TripleA_230653527350717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084874 :
    Nat.totient 3546800652308466802534084874 = 1725470587609524390421987200 := by
  rw [← show
    ((([(2, 1), (37, 1), (47929738544709010845055201, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084874 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_free64TripleA_47929738544709010845055201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084875 :
    Nat.totient 3546800652308466802534084875 = 1891614319446985822660608000 := by
  rw [← show
    ((([(3, 1), (5, 3), (149059, 1), (407047681, 1), (155884173167, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084875 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_149059, prime_lucas_407047681, prime_lucas_155884173167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084876 :
    Nat.totient 3546800652308466802534084876 = 1680063466876579763019619344 := by
  rw [← show
    ((([(2, 2), (19, 1), (263800094039, 1), (176908313113559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084876 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_free64TripleA_263800094039, prime_free64TripleA_176908313113559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084877 :
    Nat.totient 3546800652308466802534084877 = 2763740134076844779915929920 := by
  rw [← show
    ((([(7, 1), (11, 1), (4359517, 1), (10565928779237744053, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084877 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_free64TripleA_4359517, prime_free64TripleA_10565928779237744053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084878 :
    Nat.totient 3546800652308466802534084878 = 1091323066144279598269230240 := by
  rw [← show
    ((([(2, 1), (3, 1), (13, 2), (5160187, 1), (677849662823399071, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084878 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_t64_5160187, prime_lucas_677849662823399071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084879 :
    Nat.totient 3546800652308466802534084879 = 3546739374848638733447409040 := by
  rw [← show
    ((([(57881, 1), (61277459828069086617959, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084879 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_57881, prime_free64TripleA_61277459828069086617959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084880 :
    Nat.totient 3546800652308466802534084880 = 1405316356873965644335718400 := by
  rw [← show
    ((([(2, 4), (5, 1), (131, 1), (547, 1), (10135121, 1), (61046283991813, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084880 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64TripleA_131, prime_free64TripleA_547, prime_free64TripleA_10135121, prime_free64TripleA_61046283991813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084881 :
    Nat.totient 3546800652308466802534084881 = 2364533768204672812889644728 := by
  rw [← show
    ((([(3, 4), (2901032068267, 1), (15093822248003, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084881 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_2901032068267, prime_lucas_15093822248003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084882 :
    Nat.totient 3546800652308466802534084882 = 1730146659176878270043276160 := by
  rw [← show
    ((([(2, 1), (41, 1), (3561523789, 1), (12144708010980709, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084882 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_free64TripleA_3561523789, prime_free64TripleA_12144708010980709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084883 :
    Nat.totient 3546800652308466802534084883 = 3546800652308466802534084882 := by
  rw [← show
    ((([(3546800652308466802534084883, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084883 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_3546800652308466802534084883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084884 :
    Nat.totient 3546800652308466802534084884 = 1003900375594818938560390272 := by
  rw [← show
    ((([(2, 2), (3, 1), (7, 1), (107, 1), (2106407, 1), (187340392836749749, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084884 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_107, prime_t64_2106407, prime_lucas_187340392836749749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084885 :
    Nat.totient 3546800652308466802534084885 = 2670532255855786768966840320 := by
  rw [← show
    ((([(5, 1), (17, 1), (41727066497746668265106881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084885 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_free64TripleA_41727066497746668265106881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084886 :
    Nat.totient 3546800652308466802534084886 = 1723949176312172225192905800 := by
  rw [← show
    ((([(2, 1), (43, 1), (211, 1), (195459090284826782901691, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084886 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_free64TripleA_211, prime_free64TripleA_195459090284826782901691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084887 :
    Nat.totient 3546800652308466802534084887 = 2282427514147602650393600000 := by
  rw [← show
    ((([(3, 1), (29, 1), (4001, 1), (10189408545301797546401, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084887 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_4001, prime_lucas_10189408545301797546401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084888 :
    Nat.totient 3546800652308466802534084888 = 1611586141476785933512435200 := by
  rw [← show
    ((([(2, 3), (11, 1), (3469, 1), (13963, 1), (101963, 1), (8160719765141, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084888 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64TripleA_3469, prime_free64TripleA_13963, prime_free64TripleA_101963, prime_free64TripleA_8160719765141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084889 :
    Nat.totient 3546800652308466802534084889 = 3546800652237607986297342756 := by
  rw [← show
    ((([(50054507627, 1), (70858766182234507, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084889 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64TripleA_50054507627, prime_free64TripleA_70858766182234507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084890 :
    Nat.totient 3546800652308466802534084890 = 945813428727356065142069856 := by
  rw [← show
    ((([(2, 1), (3, 2), (5, 1), (12040159, 1), (3273120906190752319, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084890 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_12040159, prime_lucas_3273120906190752319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084891 :
    Nat.totient 3546800652308466802534084891 = 2806214356514226151954077696 := by
  rw [← show
    ((([(7, 1), (13, 1), (61717, 1), (92147537, 1), (6853412124269, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084891 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_free64TripleA_61717, prime_free64TripleA_92147537, prime_free64TripleA_6853412124269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084892 :
    Nat.totient 3546800652308466802534084892 = 1696295964143066029811870000 := by
  rw [← show
    ((([(2, 2), (23, 1), (381637835351, 1), (101017712166551, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084892 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_free64TripleA_381637835351, prime_free64TripleA_101017712166551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64TripleA_3546800652308466802534084893 :
    Nat.totient 3546800652308466802534084893 = 2286649324227651664859202240 := by
  rw [← show
    ((([(3, 1), (31, 1), (1423, 1), (3748763, 1), (4597727, 1), (1554954787, 1)] : List FactorBlock).map factorBlockValue).prod) = 3546800652308466802534084893 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_t64_1423, prime_t64_3748763, prime_t64_4597727, prime_lucas_1554954787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- A free-position kill four below three times `periodLcm 64`. -/
theorem freeKill_64TripleA :
    certifiedKill 1 3546800652308466802534084796 96 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free64TripleA_3546800652308466802534084797,
    phi_free64TripleA_3546800652308466802534084798,
    phi_free64TripleA_3546800652308466802534084799,
    phi_free64TripleA_3546800652308466802534084800,
    phi_free64TripleA_3546800652308466802534084801,
    phi_free64TripleA_3546800652308466802534084802,
    phi_free64TripleA_3546800652308466802534084803,
    phi_free64TripleA_3546800652308466802534084804,
    phi_free64TripleA_3546800652308466802534084805,
    phi_free64TripleA_3546800652308466802534084806,
    phi_free64TripleA_3546800652308466802534084807,
    phi_free64TripleA_3546800652308466802534084808,
    phi_free64TripleA_3546800652308466802534084809,
    phi_free64TripleA_3546800652308466802534084810,
    phi_free64TripleA_3546800652308466802534084811,
    phi_free64TripleA_3546800652308466802534084812,
    phi_free64TripleA_3546800652308466802534084813,
    phi_free64TripleA_3546800652308466802534084814,
    phi_free64TripleA_3546800652308466802534084815,
    phi_free64TripleA_3546800652308466802534084816,
    phi_free64TripleA_3546800652308466802534084817,
    phi_free64TripleA_3546800652308466802534084818,
    phi_free64TripleA_3546800652308466802534084819,
    phi_free64TripleA_3546800652308466802534084820,
    phi_free64TripleA_3546800652308466802534084821,
    phi_free64TripleA_3546800652308466802534084822,
    phi_free64TripleA_3546800652308466802534084823,
    phi_free64TripleA_3546800652308466802534084824,
    phi_free64TripleA_3546800652308466802534084825,
    phi_free64TripleA_3546800652308466802534084826,
    phi_free64TripleA_3546800652308466802534084827,
    phi_free64TripleA_3546800652308466802534084828,
    phi_free64TripleA_3546800652308466802534084829,
    phi_free64TripleA_3546800652308466802534084830,
    phi_free64TripleA_3546800652308466802534084831,
    phi_free64TripleA_3546800652308466802534084832,
    phi_free64TripleA_3546800652308466802534084833,
    phi_free64TripleA_3546800652308466802534084834,
    phi_free64TripleA_3546800652308466802534084835,
    phi_free64TripleA_3546800652308466802534084836,
    phi_free64TripleA_3546800652308466802534084837,
    phi_free64TripleA_3546800652308466802534084838,
    phi_free64TripleA_3546800652308466802534084839,
    phi_free64TripleA_3546800652308466802534084840,
    phi_free64TripleA_3546800652308466802534084841,
    phi_free64TripleA_3546800652308466802534084842,
    phi_free64TripleA_3546800652308466802534084843,
    phi_free64TripleA_3546800652308466802534084844,
    phi_free64TripleA_3546800652308466802534084845,
    phi_free64TripleA_3546800652308466802534084846,
    phi_free64TripleA_3546800652308466802534084847,
    phi_free64TripleA_3546800652308466802534084848,
    phi_free64TripleA_3546800652308466802534084849,
    phi_free64TripleA_3546800652308466802534084850,
    phi_free64TripleA_3546800652308466802534084851,
    phi_free64TripleA_3546800652308466802534084852,
    phi_free64TripleA_3546800652308466802534084853,
    phi_free64TripleA_3546800652308466802534084854,
    phi_free64TripleA_3546800652308466802534084855,
    phi_free64TripleA_3546800652308466802534084856,
    phi_free64TripleA_3546800652308466802534084857,
    phi_free64TripleA_3546800652308466802534084858,
    phi_free64TripleA_3546800652308466802534084859,
    phi_free64TripleA_3546800652308466802534084860,
    phi_free64TripleA_3546800652308466802534084861,
    phi_free64TripleA_3546800652308466802534084862,
    phi_free64TripleA_3546800652308466802534084863,
    phi_free64TripleA_3546800652308466802534084864,
    phi_free64TripleA_3546800652308466802534084865,
    phi_free64TripleA_3546800652308466802534084866,
    phi_free64TripleA_3546800652308466802534084867,
    phi_free64TripleA_3546800652308466802534084868,
    phi_free64TripleA_3546800652308466802534084869,
    phi_free64TripleA_3546800652308466802534084870,
    phi_free64TripleA_3546800652308466802534084871,
    phi_free64TripleA_3546800652308466802534084872,
    phi_free64TripleA_3546800652308466802534084873,
    phi_free64TripleA_3546800652308466802534084874,
    phi_free64TripleA_3546800652308466802534084875,
    phi_free64TripleA_3546800652308466802534084876,
    phi_free64TripleA_3546800652308466802534084877,
    phi_free64TripleA_3546800652308466802534084878,
    phi_free64TripleA_3546800652308466802534084879,
    phi_free64TripleA_3546800652308466802534084880,
    phi_free64TripleA_3546800652308466802534084881,
    phi_free64TripleA_3546800652308466802534084882,
    phi_free64TripleA_3546800652308466802534084883,
    phi_free64TripleA_3546800652308466802534084884,
    phi_free64TripleA_3546800652308466802534084885,
    phi_free64TripleA_3546800652308466802534084886,
    phi_free64TripleA_3546800652308466802534084887,
    phi_free64TripleA_3546800652308466802534084888,
    phi_free64TripleA_3546800652308466802534084889,
    phi_free64TripleA_3546800652308466802534084890,
    phi_free64TripleA_3546800652308466802534084891,
    phi_free64TripleA_3546800652308466802534084892,
    phi_free64TripleA_3546800652308466802534084893]

end TotientTailPeriodKiller
end Erdos249257
