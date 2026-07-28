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
  prime_t64_193
  prime_t64_197
  prime_t64_223
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_283
  prime_t64_307
  prime_t64_311
  prime_t64_317
  prime_t64_349
  prime_t64_383
  prime_t64_409
  prime_t64_431
  prime_t64_433
  prime_t64_439
  prime_t64_461
  prime_t64_491
  prime_t64_563
  prime_t64_607
  prime_t64_617
  prime_t64_641
  prime_t64_661
  prime_t64_761
  prime_t64_787
  prime_t64_991
  prime_t64_1051
  prime_t64_1061
  prime_t64_1093
  prime_t64_1103
  prime_t64_1213
  prime_t64_1409
  prime_t64_2281
  prime_t64_5009
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private def twentyThreeUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem twentyThreeUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    twentyThreeUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [twentyThreeUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [twentyThreeUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then twentyThreeUFastPow a n * twentyThreeUFastPow a n * a
        else twentyThreeUFastPow a n * twentyThreeUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_twentyThreeU_127 : Nat.Prime 127 := by norm_num

private theorem prime_twentyThreeU_131 : Nat.Prime 131 := by norm_num

private theorem prime_twentyThreeU_151 : Nat.Prime 151 := by norm_num

private theorem prime_twentyThreeU_173 : Nat.Prime 173 := by norm_num

private theorem prime_twentyThreeU_181 : Nat.Prime 181 := by norm_num

private theorem prime_twentyThreeU_199 : Nat.Prime 199 := by norm_num

private theorem prime_twentyThreeU_211 : Nat.Prime 211 := by norm_num

private theorem prime_twentyThreeU_257 : Nat.Prime 257 := by norm_num

private theorem prime_twentyThreeU_277 : Nat.Prime 277 := by norm_num

private theorem prime_twentyThreeU_293 : Nat.Prime 293 := by norm_num

private theorem prime_twentyThreeU_331 : Nat.Prime 331 := by norm_num

private theorem prime_twentyThreeU_337 : Nat.Prime 337 := by norm_num

private theorem prime_twentyThreeU_347 : Nat.Prime 347 := by norm_num

private theorem prime_twentyThreeU_359 : Nat.Prime 359 := by norm_num

private theorem prime_twentyThreeU_389 : Nat.Prime 389 := by norm_num

private theorem prime_twentyThreeU_397 : Nat.Prime 397 := by norm_num

private theorem prime_twentyThreeU_443 : Nat.Prime 443 := by norm_num

private theorem prime_twentyThreeU_523 : Nat.Prime 523 := by norm_num

private theorem prime_twentyThreeU_541 : Nat.Prime 541 := by norm_num

private theorem prime_twentyThreeU_557 : Nat.Prime 557 := by norm_num

private theorem prime_twentyThreeU_571 : Nat.Prime 571 := by norm_num

private theorem prime_twentyThreeU_593 : Nat.Prime 593 := by norm_num

private theorem prime_twentyThreeU_643 : Nat.Prime 643 := by norm_num

private theorem prime_twentyThreeU_653 : Nat.Prime 653 := by norm_num

private theorem prime_twentyThreeU_677 : Nat.Prime 677 := by norm_num

private theorem prime_twentyThreeU_701 : Nat.Prime 701 := by norm_num

private theorem prime_twentyThreeU_709 : Nat.Prime 709 := by norm_num

private theorem prime_twentyThreeU_733 : Nat.Prime 733 := by norm_num

private theorem prime_twentyThreeU_739 : Nat.Prime 739 := by norm_num

private theorem prime_twentyThreeU_743 : Nat.Prime 743 := by norm_num

private theorem prime_twentyThreeU_757 : Nat.Prime 757 := by norm_num

private theorem prime_twentyThreeU_769 : Nat.Prime 769 := by norm_num

private theorem prime_twentyThreeU_827 : Nat.Prime 827 := by norm_num

private theorem prime_twentyThreeU_839 : Nat.Prime 839 := by norm_num

private theorem prime_twentyThreeU_853 : Nat.Prime 853 := by norm_num

private theorem prime_twentyThreeU_877 : Nat.Prime 877 := by norm_num

private theorem prime_twentyThreeU_887 : Nat.Prime 887 := by norm_num

private theorem prime_twentyThreeU_971 : Nat.Prime 971 := by norm_num

private theorem prime_twentyThreeU_983 : Nat.Prime 983 := by norm_num

private theorem prime_twentyThreeU_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_twentyThreeU_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_twentyThreeU_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_twentyThreeU_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_twentyThreeU_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_twentyThreeU_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_twentyThreeU_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_twentyThreeU_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_twentyThreeU_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_twentyThreeU_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_twentyThreeU_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_twentyThreeU_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_twentyThreeU_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_twentyThreeU_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_twentyThreeU_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_twentyThreeU_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_twentyThreeU_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_twentyThreeU_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_twentyThreeU_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_twentyThreeU_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_twentyThreeU_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_twentyThreeU_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_twentyThreeU_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_twentyThreeU_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_twentyThreeU_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_twentyThreeU_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_twentyThreeU_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_twentyThreeU_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_twentyThreeU_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_twentyThreeU_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_twentyThreeU_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_twentyThreeU_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_twentyThreeU_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_twentyThreeU_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_twentyThreeU_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_twentyThreeU_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_twentyThreeU_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_twentyThreeU_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_twentyThreeU_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_twentyThreeU_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_twentyThreeU_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_twentyThreeU_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_twentyThreeU_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_twentyThreeU_3257 : Nat.Prime 3257 := by norm_num

private theorem prime_twentyThreeU_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_twentyThreeU_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_twentyThreeU_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_twentyThreeU_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_twentyThreeU_4877 : Nat.Prime 4877 := by norm_num

private theorem prime_twentyThreeU_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_twentyThreeU_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_twentyThreeU_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_twentyThreeU_5843 : Nat.Prime 5843 := by norm_num

private theorem prime_twentyThreeU_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_twentyThreeU_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_twentyThreeU_6359 : Nat.Prime 6359 := by norm_num

private theorem prime_twentyThreeU_6449 : Nat.Prime 6449 := by norm_num

private theorem prime_twentyThreeU_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_twentyThreeU_6689 : Nat.Prime 6689 := by norm_num

private theorem prime_twentyThreeU_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_twentyThreeU_7159 : Nat.Prime 7159 := by norm_num

private theorem prime_twentyThreeU_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_twentyThreeU_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_twentyThreeU_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_twentyThreeU_7793 : Nat.Prime 7793 := by norm_num

private theorem prime_twentyThreeU_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_twentyThreeU_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_twentyThreeU_8297 : Nat.Prime 8297 := by norm_num

private theorem prime_twentyThreeU_8573 : Nat.Prime 8573 := by norm_num

private theorem prime_twentyThreeU_8713 : Nat.Prime 8713 := by norm_num

private theorem prime_twentyThreeU_8741 : Nat.Prime 8741 := by norm_num

private theorem prime_twentyThreeU_9109 : Nat.Prime 9109 := by norm_num

private theorem prime_twentyThreeU_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_twentyThreeU_9221 : Nat.Prime 9221 := by norm_num

private theorem prime_twentyThreeU_9349 : Nat.Prime 9349 := by norm_num

private theorem prime_twentyThreeU_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_twentyThreeU_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_twentyThreeU_9679 : Nat.Prime 9679 := by norm_num

private theorem prime_twentyThreeU_9883 : Nat.Prime 9883 := by norm_num

private theorem prime_twentyThreeU_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_twentyThreeU_10193 : Nat.Prime 10193 := by norm_num

private theorem prime_twentyThreeU_10289 : Nat.Prime 10289 := by norm_num

private theorem prime_twentyThreeU_10513 : Nat.Prime 10513 := by norm_num

private theorem prime_twentyThreeU_11177 : Nat.Prime 11177 := by norm_num

private theorem prime_twentyThreeU_11273 : Nat.Prime 11273 := by norm_num

private theorem prime_twentyThreeU_11657 : Nat.Prime 11657 := by norm_num

private theorem prime_twentyThreeU_12113 : Nat.Prime 12113 := by norm_num

private theorem prime_twentyThreeU_12433 : Nat.Prime 12433 := by norm_num

private theorem prime_twentyThreeU_12613 : Nat.Prime 12613 := by norm_num

private theorem prime_twentyThreeU_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_twentyThreeU_12841 : Nat.Prime 12841 := by norm_num

private theorem prime_twentyThreeU_13177 : Nat.Prime 13177 := by norm_num

private theorem prime_twentyThreeU_13217 : Nat.Prime 13217 := by norm_num

private theorem prime_twentyThreeU_13613 : Nat.Prime 13613 := by norm_num

private theorem prime_twentyThreeU_13799 : Nat.Prime 13799 := by norm_num

private theorem prime_twentyThreeU_13883 : Nat.Prime 13883 := by norm_num

private theorem prime_twentyThreeU_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_twentyThreeU_16729 : Nat.Prime 16729 := by norm_num

private theorem prime_twentyThreeU_17033 : Nat.Prime 17033 := by norm_num

private theorem prime_twentyThreeU_18061 : Nat.Prime 18061 := by norm_num

private theorem prime_twentyThreeU_20129 : Nat.Prime 20129 := by norm_num

private theorem prime_twentyThreeU_20333 : Nat.Prime 20333 := by norm_num

private theorem prime_twentyThreeU_20507 : Nat.Prime 20507 := by norm_num

private theorem prime_twentyThreeU_20563 : Nat.Prime 20563 := by norm_num

private theorem prime_twentyThreeU_20731 : Nat.Prime 20731 := by norm_num

private theorem prime_twentyThreeU_20771 : Nat.Prime 20771 := by norm_num

private theorem prime_twentyThreeU_22397 : Nat.Prime 22397 := by norm_num

private theorem prime_twentyThreeU_23369 : Nat.Prime 23369 := by norm_num

private theorem prime_twentyThreeU_25741 : Nat.Prime 25741 := by norm_num

private theorem prime_twentyThreeU_26041 : Nat.Prime 26041 := by norm_num

private theorem prime_twentyThreeU_26339 : Nat.Prime 26339 := by norm_num

private theorem prime_twentyThreeU_27077 : Nat.Prime 27077 := by norm_num

private theorem prime_twentyThreeU_27583 : Nat.Prime 27583 := by norm_num

private theorem prime_twentyThreeU_27749 : Nat.Prime 27749 := by norm_num

private theorem prime_twentyThreeU_28949 : Nat.Prime 28949 := by norm_num

private theorem prime_twentyThreeU_32707 : Nat.Prime 32707 := by norm_num

private theorem prime_twentyThreeU_34537 : Nat.Prime 34537 := by norm_num

private theorem prime_twentyThreeU_35149 : Nat.Prime 35149 := by norm_num

private theorem prime_twentyThreeU_37013 : Nat.Prime 37013 := by norm_num

private theorem prime_twentyThreeU_38803 : Nat.Prime 38803 := by norm_num

private theorem prime_twentyThreeU_39679 : Nat.Prime 39679 := by norm_num

private theorem prime_twentyThreeU_40771 : Nat.Prime 40771 := by norm_num

private theorem prime_twentyThreeU_43661 : Nat.Prime 43661 := by norm_num

private theorem prime_twentyThreeU_43801 : Nat.Prime 43801 := by norm_num

private theorem prime_twentyThreeU_47917 : Nat.Prime 47917 := by norm_num

private theorem prime_twentyThreeU_49199 : Nat.Prime 49199 := by norm_num

private theorem prime_twentyThreeU_49459 : Nat.Prime 49459 := by norm_num

private theorem prime_twentyThreeU_49481 : Nat.Prime 49481 := by norm_num

private theorem prime_twentyThreeU_51479 : Nat.Prime 51479 := by norm_num

private theorem prime_twentyThreeU_52051 : Nat.Prime 52051 := by norm_num

private theorem prime_twentyThreeU_53597 : Nat.Prime 53597 := by norm_num

private theorem prime_twentyThreeU_53633 : Nat.Prime 53633 := by norm_num

private theorem prime_twentyThreeU_53731 : Nat.Prime 53731 := by norm_num

private theorem prime_twentyThreeU_53819 : Nat.Prime 53819 := by norm_num

private theorem prime_twentyThreeU_56437 : Nat.Prime 56437 := by norm_num

private theorem prime_twentyThreeU_57719 : Nat.Prime 57719 := by norm_num

private theorem prime_twentyThreeU_60083 : Nat.Prime 60083 := by norm_num

private theorem prime_twentyThreeU_63667 : Nat.Prime 63667 := by norm_num

private theorem prime_twentyThreeU_66593 : Nat.Prime 66593 := by norm_num

private theorem prime_twentyThreeU_67927 : Nat.Prime 67927 := by norm_num

private theorem prime_twentyThreeU_69233 : Nat.Prime 69233 := by norm_num

private theorem prime_twentyThreeU_72227 : Nat.Prime 72227 := by norm_num

private theorem prime_twentyThreeU_72671 : Nat.Prime 72671 := by norm_num

private theorem prime_twentyThreeU_74561 : Nat.Prime 74561 := by norm_num

private theorem prime_twentyThreeU_75167 : Nat.Prime 75167 := by norm_num

private theorem prime_twentyThreeU_76949 : Nat.Prime 76949 := by norm_num

private theorem prime_twentyThreeU_77017 : Nat.Prime 77017 := by norm_num

private theorem prime_twentyThreeU_84011 : Nat.Prime 84011 := by norm_num

private theorem prime_twentyThreeU_84047 : Nat.Prime 84047 := by norm_num

private theorem prime_twentyThreeU_85091 : Nat.Prime 85091 := by norm_num

private theorem prime_twentyThreeU_87107 : Nat.Prime 87107 := by norm_num

private theorem prime_twentyThreeU_89513 : Nat.Prime 89513 := by norm_num

private theorem prime_twentyThreeU_90191 : Nat.Prime 90191 := by norm_num

private theorem prime_twentyThreeU_94099 : Nat.Prime 94099 := by norm_num

private theorem prime_twentyThreeU_100511 : Nat.Prime 100511 := by norm_num

private theorem prime_twentyThreeU_101221 : Nat.Prime 101221 := by norm_num

private theorem prime_twentyThreeU_101807 : Nat.Prime 101807 := by norm_num

private theorem prime_twentyThreeU_103333 : Nat.Prime 103333 := by norm_num

private theorem prime_twentyThreeU_103573 : Nat.Prime 103573 := by norm_num

private theorem prime_twentyThreeU_104003 : Nat.Prime 104003 := by norm_num

private theorem prime_twentyThreeU_104009 : Nat.Prime 104009 := by norm_num

private theorem prime_twentyThreeU_107099 : Nat.Prime 107099 := by norm_num

private theorem prime_twentyThreeU_109579 : Nat.Prime 109579 := by norm_num

private theorem prime_twentyThreeU_112121 : Nat.Prime 112121 := by norm_num

private theorem prime_twentyThreeU_113903 : Nat.Prime 113903 := by norm_num

private theorem prime_twentyThreeU_115013 : Nat.Prime 115013 := by norm_num

private theorem prime_twentyThreeU_116381 : Nat.Prime 116381 := by norm_num

private theorem prime_twentyThreeU_116927 : Nat.Prime 116927 := by norm_num

private theorem prime_twentyThreeU_118453 : Nat.Prime 118453 := by norm_num

private theorem prime_twentyThreeU_120011 : Nat.Prime 120011 := by norm_num

private theorem prime_twentyThreeU_122147 : Nat.Prime 122147 := by norm_num

private theorem prime_twentyThreeU_122921 : Nat.Prime 122921 := by norm_num

private theorem prime_twentyThreeU_122957 : Nat.Prime 122957 := by norm_num

private theorem prime_twentyThreeU_126229 : Nat.Prime 126229 := by norm_num

private theorem prime_twentyThreeU_136303 : Nat.Prime 136303 := by norm_num

private theorem prime_twentyThreeU_140813 : Nat.Prime 140813 := by norm_num

private theorem prime_twentyThreeU_143467 : Nat.Prime 143467 := by norm_num

private theorem prime_twentyThreeU_146983 : Nat.Prime 146983 := by norm_num

private theorem prime_twentyThreeU_149323 : Nat.Prime 149323 := by norm_num

private theorem prime_twentyThreeU_163601 : Nat.Prime 163601 := by norm_num

private theorem prime_twentyThreeU_175663 : Nat.Prime 175663 := by norm_num

private theorem prime_twentyThreeU_176951 : Nat.Prime 176951 := by norm_num

private theorem prime_twentyThreeU_196541 : Nat.Prime 196541 := by norm_num

private theorem prime_twentyThreeU_198223 : Nat.Prime 198223 := by norm_num

private theorem prime_twentyThreeU_203051 : Nat.Prime 203051 := by norm_num

private theorem prime_twentyThreeU_209159 : Nat.Prime 209159 := by norm_num

private theorem prime_twentyThreeU_214691 : Nat.Prime 214691 := by norm_num

private theorem prime_twentyThreeU_222403 : Nat.Prime 222403 := by norm_num

private theorem prime_twentyThreeU_228139 : Nat.Prime 228139 := by norm_num

private theorem prime_twentyThreeU_229699 : Nat.Prime 229699 := by norm_num

private theorem prime_twentyThreeU_243311 : Nat.Prime 243311 := by norm_num

private theorem prime_twentyThreeU_244633 : Nat.Prime 244633 := by norm_num

private theorem prime_twentyThreeU_266089 : Nat.Prime 266089 := by norm_num

private theorem prime_twentyThreeU_271451 : Nat.Prime 271451 := by norm_num

private theorem prime_twentyThreeU_288979 : Nat.Prime 288979 := by norm_num

private theorem prime_twentyThreeU_294347 : Nat.Prime 294347 := by norm_num

private theorem prime_twentyThreeU_305351 : Nat.Prime 305351 := by norm_num

private theorem prime_twentyThreeU_307523 : Nat.Prime 307523 := by norm_num

private theorem prime_twentyThreeU_341293 : Nat.Prime 341293 := by norm_num

private theorem prime_twentyThreeU_349931 : Nat.Prime 349931 := by norm_num

private theorem prime_twentyThreeU_359483 : Nat.Prime 359483 := by norm_num

private theorem prime_twentyThreeU_399389 : Nat.Prime 399389 := by norm_num

private theorem prime_twentyThreeU_400943 : Nat.Prime 400943 := by norm_num

private theorem prime_twentyThreeU_463867 : Nat.Prime 463867 := by norm_num

private theorem prime_twentyThreeU_493931 : Nat.Prime 493931 := by norm_num

private theorem prime_twentyThreeU_529471 : Nat.Prime 529471 := by norm_num

private theorem prime_twentyThreeU_535939 : Nat.Prime 535939 := by norm_num

private theorem prime_twentyThreeU_546289 : Nat.Prime 546289 := by norm_num

private theorem prime_twentyThreeU_574913 : Nat.Prime 574913 := by norm_num

private theorem prime_twentyThreeU_622603 : Nat.Prime 622603 := by norm_num

private theorem prime_twentyThreeU_644197 : Nat.Prime 644197 := by norm_num

private theorem prime_twentyThreeU_647557 : Nat.Prime 647557 := by norm_num

private theorem prime_twentyThreeU_668599 : Nat.Prime 668599 := by norm_num

private theorem prime_twentyThreeU_710933 : Nat.Prime 710933 := by norm_num

private theorem prime_twentyThreeU_722581 : Nat.Prime 722581 := by norm_num

private theorem prime_twentyThreeU_723053 : Nat.Prime 723053 := by norm_num

private theorem prime_twentyThreeU_756593 : Nat.Prime 756593 := by norm_num

private theorem prime_twentyThreeU_760129 : Nat.Prime 760129 := by norm_num

private theorem prime_twentyThreeU_773803 : Nat.Prime 773803 := by norm_num

private theorem prime_twentyThreeU_811651 : Nat.Prime 811651 := by norm_num

private theorem prime_twentyThreeU_931213 : Nat.Prime 931213 := by norm_num

private theorem prime_twentyThreeU_946681 : Nat.Prime 946681 := by norm_num

private theorem prime_twentyThreeU_966233 : Nat.Prime 966233 := by norm_num

private theorem prime_twentyThreeU_989777 : Nat.Prime 989777 := by norm_num

private theorem prime_twentyThreeU_1001081 : Nat.Prime 1001081 := by norm_num

private theorem prime_twentyThreeU_1047589 : Nat.Prime 1047589 := by norm_num

private theorem prime_twentyThreeU_1076003 : Nat.Prime 1076003 := by norm_num

private theorem prime_twentyThreeU_1097909 : Nat.Prime 1097909 := by norm_num

private theorem prime_twentyThreeU_1135999 : Nat.Prime 1135999 := by norm_num

private theorem prime_twentyThreeU_1170233 : Nat.Prime 1170233 := by norm_num

private theorem prime_twentyThreeU_1216489 : Nat.Prime 1216489 := by norm_num

private theorem prime_twentyThreeU_1230067 : Nat.Prime 1230067 := by norm_num

private theorem prime_twentyThreeU_1318897 : Nat.Prime 1318897 := by norm_num

private theorem prime_twentyThreeU_1342987 : Nat.Prime 1342987 := by norm_num

private theorem prime_twentyThreeU_1365547 : Nat.Prime 1365547 := by norm_num

private theorem prime_twentyThreeU_1469231 : Nat.Prime 1469231 := by norm_num

private theorem prime_twentyThreeU_1577711 : Nat.Prime 1577711 := by norm_num

private theorem prime_twentyThreeU_1611971 : Nat.Prime 1611971 := by norm_num

private theorem prime_twentyThreeU_1627651 : Nat.Prime 1627651 := by norm_num

private theorem prime_twentyThreeU_1826183 : Nat.Prime 1826183 := by norm_num

private theorem prime_twentyThreeU_1927729 : Nat.Prime 1927729 := by norm_num

private theorem prime_twentyThreeU_1952227 : Nat.Prime 1952227 := by norm_num

private theorem prime_twentyThreeU_1969729 : Nat.Prime 1969729 := by norm_num

private theorem prime_twentyThreeU_2014897 : Nat.Prime 2014897 := by norm_num

private theorem prime_twentyThreeU_2190157 : Nat.Prime 2190157 := by norm_num

private theorem prime_twentyThreeU_2482069 : Nat.Prime 2482069 := by norm_num

private theorem prime_twentyThreeU_2573803 : Nat.Prime 2573803 := by norm_num

private theorem prime_twentyThreeU_2693363 : Nat.Prime 2693363 := by norm_num

private theorem prime_twentyThreeU_2694169 : Nat.Prime 2694169 := by norm_num

private theorem prime_twentyThreeU_2695871 : Nat.Prime 2695871 := by norm_num

private theorem prime_twentyThreeU_2936993 : Nat.Prime 2936993 := by norm_num

private theorem prime_twentyThreeU_2970797 : Nat.Prime 2970797 := by norm_num

private theorem prime_twentyThreeU_3269711 : Nat.Prime 3269711 := by norm_num

private theorem prime_twentyThreeU_3386393 : Nat.Prime 3386393 := by norm_num

private theorem prime_twentyThreeU_3826393 : Nat.Prime 3826393 := by norm_num

private theorem prime_twentyThreeU_4175803 : Nat.Prime 4175803 := by norm_num

private theorem prime_twentyThreeU_4307423 : Nat.Prime 4307423 := by norm_num

private theorem prime_twentyThreeU_4325423 : Nat.Prime 4325423 := by norm_num

private theorem prime_twentyThreeU_4350391 : Nat.Prime 4350391 := by norm_num

private theorem prime_twentyThreeU_4562707 : Nat.Prime 4562707 := by norm_num

private theorem prime_twentyThreeU_4587361 : Nat.Prime 4587361 := by norm_num

private theorem prime_twentyThreeU_4609763 : Nat.Prime 4609763 := by norm_num

private theorem prime_twentyThreeU_4661323 : Nat.Prime 4661323 := by norm_num

private theorem prime_twentyThreeU_4954841 : Nat.Prime 4954841 := by norm_num

private theorem prime_twentyThreeU_4963961 : Nat.Prime 4963961 := by norm_num

private theorem prime_twentyThreeU_4997389 : Nat.Prime 4997389 := by norm_num

private theorem prime_twentyThreeU_5044997 : Nat.Prime 5044997 := by norm_num

private theorem prime_twentyThreeU_5424319 : Nat.Prime 5424319 := by norm_num

private theorem prime_twentyThreeU_5897261 : Nat.Prime 5897261 := by norm_num

private theorem prime_twentyThreeU_5921543 : Nat.Prime 5921543 := by norm_num

private theorem prime_twentyThreeU_6187871 : Nat.Prime 6187871 := by norm_num

private theorem prime_twentyThreeU_6260129 : Nat.Prime 6260129 := by norm_num

private theorem prime_twentyThreeU_6848701 : Nat.Prime 6848701 := by norm_num

private theorem prime_twentyThreeU_7369849 : Nat.Prime 7369849 := by norm_num

private theorem prime_twentyThreeU_7399409 : Nat.Prime 7399409 := by norm_num

private theorem prime_twentyThreeU_7800211 : Nat.Prime 7800211 := by norm_num

private theorem prime_twentyThreeU_7893331 : Nat.Prime 7893331 := by norm_num

private theorem prime_twentyThreeU_8019449 : Nat.Prime 8019449 := by norm_num

private theorem prime_twentyThreeU_8781491 : Nat.Prime 8781491 := by norm_num

private theorem prime_twentyThreeU_9077903 : Nat.Prime 9077903 := by norm_num

private theorem prime_twentyThreeU_9136201 : Nat.Prime 9136201 := by norm_num

private theorem prime_twentyThreeU_9518681 : Nat.Prime 9518681 := by norm_num

private theorem prime_twentyThreeU_9662041 : Nat.Prime 9662041 := by norm_num

private theorem prime_twentyThreeU_9758999 : Nat.Prime 9758999 := by norm_num

private theorem prime_twentyThreeU_9915313 : Nat.Prime 9915313 := by norm_num

private theorem prime_twentyThreeU_10993361 : Nat.Prime 10993361 := by
  apply lucas_primality 10993361 (3 : ZMod 10993361)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (67, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (67, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) = 10993361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_67
      · exact prime_twentyThreeU_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10993361) ^ 5496680 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10993361) ^ 2198672 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10993361) ^ 1570480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10993361) ^ 164080 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10993361) ^ 37520 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_12375743 : Nat.Prime 12375743 := by
  apply lucas_primality 12375743 (5 : ZMod 12375743)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6187871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6187871, 1)] : List FactorBlock).map factorBlockValue).prod) = 12375743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_6187871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 12375743) ^ 6187871 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12375743) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_12984269 : Nat.Prime 12984269 := by
  apply lucas_primality 12984269 (2 : ZMod 12984269)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (139, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (139, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 12984269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_139
      · exact prime_t64_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12984269) ^ 6492134 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12984269) ^ 1180388 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12984269) ^ 93412 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12984269) ^ 67276 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13924759 : Nat.Prime 13924759 := by
  apply lucas_primality 13924759 (3 : ZMod 13924759)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (122147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (122147, 1)] : List FactorBlock).map factorBlockValue).prod) = 13924759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentyThreeU_122147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13924759) ^ 6962379 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13924759) ^ 4641586 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13924759) ^ 732882 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13924759) ^ 114 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_14521601 : Nat.Prime 14521601 := by
  apply lucas_primality 14521601 (3 : ZMod 14521601)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 14521601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14521601) ^ 7260800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14521601) ^ 2904320 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14521601) ^ 6400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15404087 : Nat.Prime 15404087 := by
  apply lucas_primality 15404087 (5 : ZMod 15404087)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (61, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (61, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) = 15404087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_61
      · exact prime_twentyThreeU_4073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15404087) ^ 7702043 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 15404087) ^ 496906 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 15404087) ^ 252526 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 15404087) ^ 3782 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15460729 : Nat.Prime 15460729 := by
  apply lucas_primality 15460729 (23 : ZMod 15460729)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (644197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (644197, 1)] : List FactorBlock).map factorBlockValue).prod) = 15460729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_644197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 15460729) ^ 7730364 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 15460729) ^ 5153576 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 15460729) ^ 24 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_17042393 : Nat.Prime 17042393 := by
  apply lucas_primality 17042393 (3 : ZMod 17042393)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (112121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (112121, 1)] : List FactorBlock).map factorBlockValue).prod) = 17042393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentyThreeU_112121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17042393) ^ 8521196 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17042393) ^ 896968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17042393) ^ 152 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_17199463 : Nat.Prime 17199463 := by
  apply lucas_primality 17199463 (3 : ZMod 17199463)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (8713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (8713, 1)] : List FactorBlock).map factorBlockValue).prod) = 17199463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_twentyThreeU_8713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17199463) ^ 8599731 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199463) ^ 5733154 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199463) ^ 2457066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199463) ^ 365946 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 17199463) ^ 1974 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_18242129 : Nat.Prime 18242129 := by
  apply lucas_primality 18242129 (6 : ZMod 18242129)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (23, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (23, 1), (2609, 1)] : List FactorBlock).map factorBlockValue).prod) = 18242129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_twentyThreeU_2609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 18242129) ^ 9121064 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 18242129) ^ 960112 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 18242129) ^ 793136 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 18242129) ^ 6992 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_18769073 : Nat.Prime 18769073 := by
  apply lucas_primality 18769073 (3 : ZMod 18769073)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (103, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (103, 1), (1627, 1)] : List FactorBlock).map factorBlockValue).prod) = 18769073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_103
      · exact prime_twentyThreeU_1627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18769073) ^ 9384536 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769073) ^ 2681296 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769073) ^ 182224 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18769073) ^ 11536 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_22051483 : Nat.Prime 22051483 := by
  apply lucas_primality 22051483 (11 : ZMod 22051483)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (5843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (5843, 1)] : List FactorBlock).map factorBlockValue).prod) = 22051483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_37
      · exact prime_twentyThreeU_5843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22051483) ^ 11025741 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 22051483) ^ 7350494 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 22051483) ^ 1297146 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 22051483) ^ 595986 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 22051483) ^ 3774 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_22958359 : Nat.Prime 22958359 := by
  apply lucas_primality 22958359 (7 : ZMod 22958359)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3826393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3826393, 1)] : List FactorBlock).map factorBlockValue).prod) = 22958359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_3826393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 22958359) ^ 11479179 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 22958359) ^ 7652786 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 22958359) ^ 6 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_25054819 : Nat.Prime 25054819 := by
  apply lucas_primality 25054819 (3 : ZMod 25054819)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4175803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4175803, 1)] : List FactorBlock).map factorBlockValue).prod) = 25054819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_4175803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25054819) ^ 12527409 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25054819) ^ 8351606 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 25054819) ^ 6 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_28337723 : Nat.Prime 28337723 := by
  apply lucas_primality 28337723 (2 : ZMod 28337723)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (181, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (181, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 28337723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_twentyThreeU_181
      · exact prime_twentyThreeU_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28337723) ^ 14168861 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28337723) ^ 4048246 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28337723) ^ 534674 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28337723) ^ 156562 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28337723) ^ 134302 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_28773881 : Nat.Prime 28773881 := by
  apply lucas_primality 28773881 (3 : ZMod 28773881)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (16729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (16729, 1)] : List FactorBlock).map factorBlockValue).prod) = 28773881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_twentyThreeU_16729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28773881) ^ 14386940 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 28773881) ^ 5754776 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 28773881) ^ 669160 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 28773881) ^ 1720 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_29875883 : Nat.Prime 29875883 := by
  apply lucas_primality 29875883 (2 : ZMod 29875883)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (877, 1), (17033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (877, 1), (17033, 1)] : List FactorBlock).map factorBlockValue).prod) = 29875883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_877
      · exact prime_twentyThreeU_17033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29875883) ^ 14937941 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29875883) ^ 34066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29875883) ^ 1754 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_31874369 : Nat.Prime 31874369 := by
  apply lucas_primality 31874369 (3 : ZMod 31874369)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (139, 1), (3583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (139, 1), (3583, 1)] : List FactorBlock).map factorBlockValue).prod) = 31874369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_twentyThreeU_3583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31874369) ^ 15937184 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 31874369) ^ 229312 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 31874369) ^ 8896 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_35008291 : Nat.Prime 35008291 := by
  apply lucas_primality 35008291 (2 : ZMod 35008291)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (10513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (10513, 1)] : List FactorBlock).map factorBlockValue).prod) = 35008291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_twentyThreeU_10513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35008291) ^ 17504145 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35008291) ^ 11669430 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35008291) ^ 7001658 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35008291) ^ 946170 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35008291) ^ 3330 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_35570789 : Nat.Prime 35570789 := by
  apply lucas_primality 35570789 (2 : ZMod 35570789)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (35149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (35149, 1)] : List FactorBlock).map factorBlockValue).prod) = 35570789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentyThreeU_35149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35570789) ^ 17785394 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35570789) ^ 3233708 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35570789) ^ 1546556 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 35570789) ^ 1012 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_39163573 : Nat.Prime 39163573 := by
  apply lucas_primality 39163573 (2 : ZMod 39163573)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (29, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (29, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 39163573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39163573) ^ 19581786 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39163573) ^ 13054524 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39163573) ^ 5594796 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39163573) ^ 1702764 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39163573) ^ 1350468 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 39163573) ^ 168084 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_39333383 : Nat.Prime 39333383 := by
  apply lucas_primality 39333383 (5 : ZMod 39333383)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (94099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (94099, 1)] : List FactorBlock).map factorBlockValue).prod) = 39333383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_twentyThreeU_94099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39333383) ^ 19666691 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 39333383) ^ 3575762 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 39333383) ^ 2070178 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 39333383) ^ 418 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_40374097 : Nat.Prime 40374097 := by
  apply lucas_primality 40374097 (5 : ZMod 40374097)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (107, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (107, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) = 40374097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_107
      · exact prime_twentyThreeU_1123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40374097) ^ 20187048 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40374097) ^ 13458032 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40374097) ^ 5767728 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40374097) ^ 377328 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 40374097) ^ 35952 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_44651977 : Nat.Prime 44651977 := by
  apply lucas_primality 44651977 (5 : ZMod 44651977)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (181, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (181, 1), (541, 1)] : List FactorBlock).map factorBlockValue).prod) = 44651977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentyThreeU_181
      · exact prime_twentyThreeU_541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44651977) ^ 22325988 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44651977) ^ 14883992 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44651977) ^ 2350104 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44651977) ^ 246696 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 44651977) ^ 82536 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_45098231 : Nat.Prime 45098231 := by
  apply lucas_primality 45098231 (29 : ZMod 45098231)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (85091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (85091, 1)] : List FactorBlock).map factorBlockValue).prod) = 45098231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_twentyThreeU_85091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 45098231) ^ 22549115 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 9019646 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 850910 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 45098231) ^ 530 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_46324247 : Nat.Prime 46324247 := by
  apply lucas_primality 46324247 (5 : ZMod 46324247)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (120011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (120011, 1)] : List FactorBlock).map factorBlockValue).prod) = 46324247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_193
      · exact prime_twentyThreeU_120011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 46324247) ^ 23162123 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 46324247) ^ 240022 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 46324247) ^ 386 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_46760033 : Nat.Prime 46760033 := by
  apply lucas_primality 46760033 (3 : ZMod 46760033)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (71, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (71, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 46760033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_71
      · exact prime_twentyThreeU_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46760033) ^ 23380016 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 4250912 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 658592 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 46760033) ^ 24992 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_47855501 : Nat.Prime 47855501 := by
  apply lucas_primality 47855501 (2 : ZMod 47855501)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (11, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (11, 2), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 47855501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47855501) ^ 23927750 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 9571100 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 6836500 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 4350500 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47855501) ^ 423500 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_54527953 : Nat.Prime 54527953 := by
  apply lucas_primality 54527953 (5 : ZMod 54527953)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1135999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1135999, 1)] : List FactorBlock).map factorBlockValue).prod) = 54527953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_1135999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 54527953) ^ 27263976 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 54527953) ^ 18175984 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 54527953) ^ 48 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_56041753 : Nat.Prime 56041753 := by
  apply lucas_primality 56041753 (5 : ZMod 56041753)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (41, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 56041753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_twentyThreeU_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56041753) ^ 28020876 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 18680584 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 4310904 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 1366872 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 56041753) ^ 166296 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_57298999 : Nat.Prime 57298999 := by
  apply lucas_primality 57298999 (3 : ZMod 57298999)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (49481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (49481, 1)] : List FactorBlock).map factorBlockValue).prod) = 57298999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_193
      · exact prime_twentyThreeU_49481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57298999) ^ 28649499 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 19099666 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 296886 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57298999) ^ 1158 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_63269953 : Nat.Prime 63269953 := by
  apply lucas_primality 63269953 (5 : ZMod 63269953)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (229, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (229, 1), (1439, 1)] : List FactorBlock).map factorBlockValue).prod) = 63269953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_229
      · exact prime_twentyThreeU_1439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63269953) ^ 31634976 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 21089984 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 276288 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 63269953) ^ 43968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_63748739 : Nat.Prime 63748739 := by
  apply lucas_primality 63748739 (2 : ZMod 63748739)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31874369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31874369, 1)] : List FactorBlock).map factorBlockValue).prod) = 63748739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_31874369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 63748739) ^ 31874369 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 63748739) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_64400449 : Nat.Prime 64400449 := by
  apply lucas_primality 64400449 (17 : ZMod 64400449)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (47917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (47917, 1)] : List FactorBlock).map factorBlockValue).prod) = 64400449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_47917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 64400449) ^ 32200224 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 64400449) ^ 21466816 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 64400449) ^ 9200064 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 64400449) ^ 1344 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_64998337 : Nat.Prime 64998337 := by
  apply lucas_primality 64998337 (5 : ZMod 64998337)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13, 1), (26041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13, 1), (26041, 1)] : List FactorBlock).map factorBlockValue).prod) = 64998337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyThreeU_26041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64998337) ^ 32499168 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 21666112 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 4999872 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64998337) ^ 2496 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_70143883 : Nat.Prime 70143883 := by
  apply lucas_primality 70143883 (2 : ZMod 70143883)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (71, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (71, 1), (7159, 1)] : List FactorBlock).map factorBlockValue).prod) = 70143883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_71
      · exact prime_twentyThreeU_7159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70143883) ^ 35071941 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70143883) ^ 23381294 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70143883) ^ 3049734 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70143883) ^ 987942 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 70143883) ^ 9798 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_71232151 : Nat.Prime 71232151 := by
  apply lucas_primality 71232151 (7 : ZMod 71232151)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (23, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (23, 1), (1877, 1)] : List FactorBlock).map factorBlockValue).prod) = 71232151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentyThreeU_1877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 71232151) ^ 35616075 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71232151) ^ 23744050 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71232151) ^ 14246430 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71232151) ^ 6475650 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71232151) ^ 3097050 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71232151) ^ 37950 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_80800891 : Nat.Prime 80800891 := by
  apply lucas_primality 80800891 (2 : ZMod 80800891)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2693363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2693363, 1)] : List FactorBlock).map factorBlockValue).prod) = 80800891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_2693363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80800891) ^ 40400445 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 80800891) ^ 26933630 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 80800891) ^ 16160178 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 80800891) ^ 30 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_87006637 : Nat.Prime 87006637 := by
  apply lucas_primality 87006637 (6 : ZMod 87006637)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (89513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (89513, 1)] : List FactorBlock).map factorBlockValue).prod) = 87006637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_89513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 87006637) ^ 43503318 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 87006637) ^ 29002212 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 87006637) ^ 972 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_87654641 : Nat.Prime 87654641 := by
  apply lucas_primality 87654641 (3 : ZMod 87654641)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (43, 1), (83, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (43, 1), (83, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) = 87654641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_t64_83
      · exact prime_t64_307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87654641) ^ 43827320 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 87654641) ^ 17530928 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 87654641) ^ 2038480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 87654641) ^ 1056080 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 87654641) ^ 285520 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_87946889 : Nat.Prime 87946889 := by
  apply lucas_primality 87946889 (3 : ZMod 87946889)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (10993361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (10993361, 1)] : List FactorBlock).map factorBlockValue).prod) = 87946889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_10993361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 87946889) ^ 43973444 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 87946889) ^ 8 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_93520067 : Nat.Prime 93520067 := by
  apply lucas_primality 93520067 (2 : ZMod 93520067)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46760033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46760033, 1)] : List FactorBlock).map factorBlockValue).prod) = 93520067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_46760033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 93520067) ^ 46760033 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 93520067) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_116858741 : Nat.Prime 116858741 := by
  apply lucas_primality 116858741 (2 : ZMod 116858741)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (307523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (307523, 1)] : List FactorBlock).map factorBlockValue).prod) = 116858741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_twentyThreeU_307523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116858741) ^ 58429370 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116858741) ^ 23371748 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116858741) ^ 6150460 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 116858741) ^ 380 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_127090643 : Nat.Prime 127090643 := by
  apply lucas_primality 127090643 (2 : ZMod 127090643)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9077903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9077903, 1)] : List FactorBlock).map factorBlockValue).prod) = 127090643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_9077903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 127090643) ^ 63545321 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 127090643) ^ 18155806 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 127090643) ^ 14 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_137881031 : Nat.Prime 137881031 := by
  apply lucas_primality 137881031 (7 : ZMod 137881031)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1969729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1969729, 1)] : List FactorBlock).map factorBlockValue).prod) = 137881031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_1969729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 137881031) ^ 68940515 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 27576206 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 19697290 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 137881031) ^ 70 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_142184897 : Nat.Prime 142184897 := by
  apply lucas_primality 142184897 (5 : ZMod 142184897)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (23, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (23, 1), (13799, 1)] : List FactorBlock).map factorBlockValue).prod) = 142184897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_twentyThreeU_13799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 142184897) ^ 71092448 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 20312128 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 6181952 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 142184897) ^ 10304 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_144684511 : Nat.Prime 144684511 := by
  apply lucas_primality 144684511 (3 : ZMod 144684511)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (67927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (67927, 1)] : List FactorBlock).map factorBlockValue).prod) = 144684511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_twentyThreeU_67927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144684511) ^ 72342255 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144684511) ^ 48228170 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144684511) ^ 28936902 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144684511) ^ 2037810 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 144684511) ^ 2130 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_149921671 : Nat.Prime 149921671 := by
  apply lucas_primality 149921671 (3 : ZMod 149921671)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4997389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4997389, 1)] : List FactorBlock).map factorBlockValue).prod) = 149921671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_4997389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 149921671) ^ 74960835 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 49973890 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 29984334 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 149921671) ^ 30 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_170365511 : Nat.Prime 170365511 := by
  apply lucas_primality 170365511 (14 : ZMod 170365511)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1087, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1087, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) = 170365511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_1087
      · exact prime_twentyThreeU_2239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 170365511) ^ 85182755 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 34073102 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 24337930 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 156730 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 170365511) ^ 76090 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_177900851 : Nat.Prime 177900851 := by
  apply lucas_primality 177900851 (2 : ZMod 177900851)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (197, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (197, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 177900851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_197
      · exact prime_twentyThreeU_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 177900851) ^ 88950425 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 35580170 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 903050 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 177900851) ^ 9850 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_188983007 : Nat.Prime 188983007 := by
  apply lucas_primality 188983007 (5 : ZMod 188983007)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (137, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (137, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 188983007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_31
      · exact prime_t64_137
      · exact prime_twentyThreeU_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 188983007) ^ 94491503 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 9946474 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 6096226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 1379438 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 188983007) ^ 161386 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_190251689 : Nat.Prime 190251689 := by
  apply lucas_primality 190251689 (3 : ZMod 190251689)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (196541, 1)] : List FactorBlock).map factorBlockValue).prod) = 190251689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentyThreeU_196541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 190251689) ^ 95125844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 190251689) ^ 17295608 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 190251689) ^ 968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_216664841 : Nat.Prime 216664841 := by
  apply lucas_primality 216664841 (3 : ZMod 216664841)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (773803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (773803, 1)] : List FactorBlock).map factorBlockValue).prod) = 216664841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_773803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 216664841) ^ 108332420 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 216664841) ^ 43332968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 216664841) ^ 30952120 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 216664841) ^ 280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_259185373 : Nat.Prime 259185373 := by
  apply lucas_primality 259185373 (5 : ZMod 259185373)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3229, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3229, 1), (6689, 1)] : List FactorBlock).map factorBlockValue).prod) = 259185373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_3229
      · exact prime_twentyThreeU_6689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 259185373) ^ 129592686 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 259185373) ^ 86395124 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 259185373) ^ 80268 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 259185373) ^ 38748 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_276055733 : Nat.Prime 276055733 := by
  apply lucas_primality 276055733 (2 : ZMod 276055733)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (116381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (116381, 1)] : List FactorBlock).map factorBlockValue).prod) = 276055733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_593
      · exact prime_twentyThreeU_116381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276055733) ^ 138027866 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 276055733) ^ 465524 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 276055733) ^ 2372 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_279560689 : Nat.Prime 279560689 := by
  apply lucas_primality 279560689 (13 : ZMod 279560689)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (529471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (529471, 1)] : List FactorBlock).map factorBlockValue).prod) = 279560689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyThreeU_529471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 279560689) ^ 139780344 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 93186896 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 25414608 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 279560689) ^ 528 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_287645443 : Nat.Prime 287645443 := by
  apply lucas_primality 287645443 (5 : ZMod 287645443)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6848701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6848701, 1)] : List FactorBlock).map factorBlockValue).prod) = 287645443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_6848701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 287645443) ^ 143822721 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 95881814 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 41092206 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 287645443) ^ 42 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_301794113 : Nat.Prime 301794113 := by
  apply lucas_primality 301794113 (5 : ZMod 301794113)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41, 1), (115013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41, 1), (115013, 1)] : List FactorBlock).map factorBlockValue).prod) = 301794113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_twentyThreeU_115013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 301794113) ^ 150897056 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 301794113) ^ 7360832 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 301794113) ^ 2624 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_308793623 : Nat.Prime 308793623 := by
  apply lucas_primality 308793623 (5 : ZMod 308793623)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1409, 1), (109579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1409, 1), (109579, 1)] : List FactorBlock).map factorBlockValue).prod) = 308793623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_1409
      · exact prime_twentyThreeU_109579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 308793623) ^ 154396811 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 308793623) ^ 219158 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 308793623) ^ 2818 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_319858361 : Nat.Prime 319858361 := by
  apply lucas_primality 319858361 (6 : ZMod 319858361)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (79, 1), (101221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (79, 1), (101221, 1)] : List FactorBlock).map factorBlockValue).prod) = 319858361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_twentyThreeU_101221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 319858361) ^ 159929180 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 319858361) ^ 63971672 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 319858361) ^ 4048840 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 319858361) ^ 3160 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_365866097 : Nat.Prime 365866097 := by
  apply lucas_primality 365866097 (3 : ZMod 365866097)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (341293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (341293, 1)] : List FactorBlock).map factorBlockValue).prod) = 365866097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_twentyThreeU_341293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 365866097) ^ 182933048 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 365866097) ^ 5460688 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 365866097) ^ 1072 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_380562029 : Nat.Prime 380562029 := by
  apply lucas_primality 380562029 (3 : ZMod 380562029)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (199, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (199, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) = 380562029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyThreeU_199
      · exact prime_twentyThreeU_887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 380562029) ^ 190281014 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 380562029) ^ 54366004 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 380562029) ^ 34596548 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 380562029) ^ 1912372 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 380562029) ^ 429044 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_401513269 : Nat.Prime 401513269 := by
  apply lucas_primality 401513269 (2 : ZMod 401513269)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2573803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2573803, 1)] : List FactorBlock).map factorBlockValue).prod) = 401513269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyThreeU_2573803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 401513269) ^ 200756634 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 133837756 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 30885636 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 401513269) ^ 156 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_429711563 : Nat.Prime 429711563 := by
  apply lucas_primality 429711563 (2 : ZMod 429711563)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (43661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (43661, 1)] : List FactorBlock).map factorBlockValue).prod) = 429711563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_37
      · exact prime_twentyThreeU_43661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429711563) ^ 214855781 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429711563) ^ 61387366 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429711563) ^ 22616398 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429711563) ^ 11613826 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 429711563) ^ 9842 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_463780391 : Nat.Prime 463780391 := by
  apply lucas_primality 463780391 (7 : ZMod 463780391)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (617, 1), (75167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (617, 1), (75167, 1)] : List FactorBlock).map factorBlockValue).prod) = 463780391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_617
      · exact prime_twentyThreeU_75167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 463780391) ^ 231890195 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 463780391) ^ 92756078 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 463780391) ^ 751670 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 463780391) ^ 6170 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_509146541 : Nat.Prime 509146541 := by
  apply lucas_primality 509146541 (10 : ZMod 509146541)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (389, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (389, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) = 509146541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_389
      · exact prime_twentyThreeU_9349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 509146541) ^ 254573270 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 509146541) ^ 101829308 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 509146541) ^ 72735220 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 509146541) ^ 1308860 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 509146541) ^ 54460 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_540402979 : Nat.Prime 540402979 := by
  apply lucas_primality 540402979 (2 : ZMod 540402979)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (2053, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (2053, 1), (2309, 1)] : List FactorBlock).map factorBlockValue).prod) = 540402979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_twentyThreeU_2053
      · exact prime_twentyThreeU_2309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 540402979) ^ 270201489 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 180134326 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 28442262 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 263226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 540402979) ^ 234042 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_574463957 : Nat.Prime 574463957 := by
  apply lucas_primality 574463957 (2 : ZMod 574463957)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (41, 1), (28949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (41, 1), (28949, 1)] : List FactorBlock).map factorBlockValue).prod) = 574463957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_twentyThreeU_28949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 574463957) ^ 287231978 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 52223996 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 14011316 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574463957) ^ 19844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_604483333 : Nat.Prime 604483333 := by
  apply lucas_primality 604483333 (2 : ZMod 604483333)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (2190157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (2190157, 1)] : List FactorBlock).map factorBlockValue).prod) = 604483333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_twentyThreeU_2190157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 604483333) ^ 302241666 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 201494444 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 26281884 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 604483333) ^ 276 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_604694273 : Nat.Prime 604694273 := by
  apply lucas_primality 604694273 (3 : ZMod 604694273)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7, 1), (13, 1), (101, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7, 1), (13, 1), (101, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 604694273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_101
      · exact prime_twentyThreeU_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 604694273) ^ 302347136 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 86384896 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 46514944 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 5987072 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 604694273) ^ 2352896 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_649983371 : Nat.Prime 649983371 := by
  apply lucas_primality 649983371 (2 : ZMod 649983371)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (64998337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (64998337, 1)] : List FactorBlock).map factorBlockValue).prod) = 649983371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_64998337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 649983371) ^ 324991685 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 649983371) ^ 129996674 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 649983371) ^ 10 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_836693087 : Nat.Prime 836693087 := by
  apply lucas_primality 836693087 (5 : ZMod 836693087)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (7893331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (7893331, 1)] : List FactorBlock).map factorBlockValue).prod) = 836693087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_twentyThreeU_7893331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 836693087) ^ 418346543 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 836693087) ^ 15786662 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 836693087) ^ 106 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_859423127 : Nat.Prime 859423127 := by
  apply lucas_primality 859423127 (5 : ZMod 859423127)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (429711563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (429711563, 1)] : List FactorBlock).map factorBlockValue).prod) = 859423127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_429711563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 859423127) ^ 429711563 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 859423127) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_920562037 : Nat.Prime 920562037 := by
  apply lucas_primality 920562037 (2 : ZMod 920562037)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (79, 1), (239, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (79, 1), (239, 2)] : List FactorBlock).map factorBlockValue).prod) = 920562037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_79
      · exact prime_t64_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 920562037) ^ 460281018 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 920562037) ^ 306854012 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 920562037) ^ 54150708 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 920562037) ^ 11652684 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 920562037) ^ 3851724 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_941297459 : Nat.Prime 941297459 := by
  apply lucas_primality 941297459 (2 : ZMod 941297459)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (151, 1), (27583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (151, 1), (27583, 1)] : List FactorBlock).map factorBlockValue).prod) = 941297459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_113
      · exact prime_twentyThreeU_151
      · exact prime_twentyThreeU_27583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 941297459) ^ 470648729 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 8330066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 6233758 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 941297459) ^ 34126 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1009161947 : Nat.Prime 1009161947 := by
  apply lucas_primality 1009161947 (2 : ZMod 1009161947)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (946681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (946681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1009161947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_twentyThreeU_946681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1009161947) ^ 504580973 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 77627842 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 24613706 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1009161947) ^ 1066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1099968451 : Nat.Prime 1099968451 := by
  apply lucas_primality 1099968451 (3 : ZMod 1099968451)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (1047589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (1047589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1099968451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_1047589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1099968451) ^ 549984225 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099968451) ^ 366656150 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099968451) ^ 219993690 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099968451) ^ 157138350 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1099968451) ^ 1050 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1137479177 : Nat.Prime 1137479177 := by
  apply lucas_primality 1137479177 (3 : ZMod 1137479177)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (142184897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (142184897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137479177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_142184897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1137479177) ^ 568739588 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1137479177) ^ 8 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1140538079 : Nat.Prime 1140538079 := by
  apply lucas_primality 1140538079 (7 : ZMod 1140538079)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7411, 1), (76949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7411, 1), (76949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140538079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_7411
      · exact prime_twentyThreeU_76949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1140538079) ^ 570269039 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1140538079) ^ 153898 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1140538079) ^ 14822 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1157796803 : Nat.Prime 1157796803 := by
  apply lucas_primality 1157796803 (2 : ZMod 1157796803)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2851, 1), (203051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2851, 1), (203051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1157796803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_2851
      · exact prime_twentyThreeU_203051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1157796803) ^ 578898401 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157796803) ^ 406102 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1157796803) ^ 5702 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1209388547 : Nat.Prime 1209388547 := by
  apply lucas_primality 1209388547 (2 : ZMod 1209388547)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (604694273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (604694273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1209388547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_604694273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1209388547) ^ 604694273 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1209388547) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1220738251 : Nat.Prime 1220738251 := by
  apply lucas_primality 1220738251 (2 : ZMod 1220738251)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (1627651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (1627651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1220738251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_1627651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1220738251) ^ 610369125 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 406912750 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 244147650 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220738251) ^ 750 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1282178719 : Nat.Prime 1282178719 := by
  apply lucas_primality 1282178719 (3 : ZMod 1282178719)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71232151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71232151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1282178719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_71232151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1282178719) ^ 641089359 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282178719) ^ 427392906 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1282178719) ^ 18 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1370511479 : Nat.Prime 1370511479 := by
  apply lucas_primality 1370511479 (7 : ZMod 1370511479)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (2281, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (2281, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370511479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_2281
      · exact prime_twentyThreeU_6131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1370511479) ^ 685255739 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370511479) ^ 195787354 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370511479) ^ 600838 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370511479) ^ 223538 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1379682971 : Nat.Prime 1379682971 := by
  apply lucas_primality 1379682971 (2 : ZMod 1379682971)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1093, 1), (126229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1093, 1), (126229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1379682971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_1093
      · exact prime_twentyThreeU_126229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1379682971) ^ 689841485 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379682971) ^ 275936594 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379682971) ^ 1262290 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1379682971) ^ 10930 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1526091029 : Nat.Prime 1526091029 := by
  apply lucas_primality 1526091029 (2 : ZMod 1526091029)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (4954841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (4954841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1526091029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyThreeU_4954841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1526091029) ^ 763045514 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526091029) ^ 218013004 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526091029) ^ 138735548 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1526091029) ^ 308 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1584080819 : Nat.Prime 1584080819 := by
  apply lucas_primality 1584080819 (2 : ZMod 1584080819)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (12984269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (12984269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1584080819 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_61
      · exact prime_twentyThreeU_12984269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1584080819) ^ 792040409 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584080819) ^ 25968538 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1584080819) ^ 122 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1703927881 : Nat.Prime 1703927881 := by
  apply lucas_primality 1703927881 (17 : ZMod 1703927881)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (1577711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (1577711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1703927881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_1577711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1703927881) ^ 851963940 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 567975960 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 340785576 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 1703927881) ^ 1080 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1810764679 : Nat.Prime 1810764679 := by
  apply lucas_primality 1810764679 (3 : ZMod 1810764679)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (301794113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (301794113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1810764679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_301794113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1810764679) ^ 905382339 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1810764679) ^ 603588226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1810764679) ^ 6 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1872272351 : Nat.Prime 1872272351 := by
  apply lucas_primality 1872272351 (19 : ZMod 1872272351)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (19, 2), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (19, 2), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1872272351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_79
      · exact prime_t64_101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1872272351) ^ 936136175 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1872272351) ^ 374454470 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1872272351) ^ 144020950 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1872272351) ^ 98540650 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1872272351) ^ 23699650 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (19 : ZMod 1872272351) ^ 18537350 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2384892023 : Nat.Prime 2384892023 := by
  apply lucas_primality 2384892023 (5 : ZMod 2384892023)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (70143883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (70143883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2384892023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyThreeU_70143883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2384892023) ^ 1192446011 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2384892023) ^ 140287766 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2384892023) ^ 34 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2413558747 : Nat.Prime 2413558747 := by
  apply lucas_primality 2413558747 (2 : ZMod 2413558747)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1741, 1), (77017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1741, 1), (77017, 1)] : List FactorBlock).map factorBlockValue).prod) = 2413558747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_1741
      · exact prime_twentyThreeU_77017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2413558747) ^ 1206779373 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 804519582 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 1386306 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2413558747) ^ 31338 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2591853731 : Nat.Prime 2591853731 := by
  apply lucas_primality 2591853731 (2 : ZMod 2591853731)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (259185373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (259185373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2591853731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_259185373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2591853731) ^ 1295926865 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2591853731) ^ 518370746 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2591853731) ^ 10 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2844774137 : Nat.Prime 2844774137 := by
  apply lucas_primality 2844774137 (3 : ZMod 2844774137)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (15460729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (15460729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844774137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyThreeU_15460729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2844774137) ^ 1422387068 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844774137) ^ 123685832 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2844774137) ^ 184 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2960967601 : Nat.Prime 2960967601 := by
  apply lucas_primality 2960967601 (52 : ZMod 2960967601)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (19, 1), (73, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (19, 1), (73, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2960967601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_73
      · exact prime_twentyThreeU_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (52 : ZMod 2960967601) ^ 1480483800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 986989200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 592193520 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 155840400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 40561200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (52 : ZMod 2960967601) ^ 4993200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3111229777 : Nat.Prime 3111229777 := by
  apply lucas_primality 3111229777 (5 : ZMod 3111229777)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (6359, 1), (10193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (6359, 1), (10193, 1)] : List FactorBlock).map factorBlockValue).prod) = 3111229777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_6359
      · exact prime_twentyThreeU_10193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3111229777) ^ 1555614888 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3111229777) ^ 1037076592 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3111229777) ^ 489264 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3111229777) ^ 305232 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3330424087 : Nat.Prime 3330424087 := by
  apply lucas_primality 3330424087 (7 : ZMod 3330424087)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (4587361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (4587361, 1)] : List FactorBlock).map factorBlockValue).prod) = 3330424087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyThreeU_4587361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3330424087) ^ 1665212043 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 1110141362 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 302765826 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 3330424087) ^ 726 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3746573059 : Nat.Prime 3746573059 := by
  apply lucas_primality 3746573059 (2 : ZMod 3746573059)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (14521601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (14521601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746573059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyThreeU_14521601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3746573059) ^ 1873286529 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 1248857686 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 87129606 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3746573059) ^ 258 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3800098483 : Nat.Prime 3800098483 := by
  apply lucas_primality 3800098483 (3 : ZMod 3800098483)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (139, 1), (146983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (139, 1), (146983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3800098483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_139
      · exact prime_twentyThreeU_146983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3800098483) ^ 1900049241 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3800098483) ^ 1266699494 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3800098483) ^ 122583822 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3800098483) ^ 27338838 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3800098483) ^ 25854 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_4256140153 : Nat.Prime 4256140153 := by
  apply lucas_primality 4256140153 (7 : ZMod 4256140153)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (337, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (337, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4256140153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyThreeU_337
      · exact prime_twentyThreeU_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4256140153) ^ 2128070076 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 1418713384 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 386921832 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 12629496 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4256140153) ^ 978648 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_4289167079 : Nat.Prime 4289167079 := by
  apply lucas_primality 4289167079 (13 : ZMod 4289167079)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (47, 1), (931213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (47, 1), (931213, 1)] : List FactorBlock).map factorBlockValue).prod) = 4289167079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_47
      · exact prime_twentyThreeU_931213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4289167079) ^ 2144583539 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 4289167079) ^ 612738154 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 4289167079) ^ 91258874 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 4289167079) ^ 4606 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_6335859269 : Nat.Prime 6335859269 := by
  apply lucas_primality 6335859269 (2 : ZMod 6335859269)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (7993, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (7993, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) = 6335859269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyThreeU_7993
      · exact prime_twentyThreeU_11657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6335859269) ^ 3167929634 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 372697604 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 792676 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6335859269) ^ 543524 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7241186041 : Nat.Prime 7241186041 := by
  apply lucas_primality 7241186041 (13 : ZMod 7241186041)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (17, 1), (523, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (17, 1), (523, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 7241186041 - 1 by
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
      · exact prime_twentyThreeU_523
      · exact prime_t64_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7241186041) ^ 3620593020 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 2413728680 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 1448237208 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 658289640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 425952120 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 13845480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 7241186041) ^ 11736120 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7243058717 : Nat.Prime 7243058717 := by
  apply lucas_primality 7243058717 (2 : ZMod 7243058717)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1810764679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1810764679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7243058717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_1810764679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7243058717) ^ 3621529358 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7243058717) ^ 4 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7423661299 : Nat.Prime 7423661299 := by
  apply lucas_primality 7423661299 (2 : ZMod 7423661299)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (28773881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (28773881, 1)] : List FactorBlock).map factorBlockValue).prod) = 7423661299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_twentyThreeU_28773881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7423661299) ^ 3711830649 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423661299) ^ 2474553766 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423661299) ^ 172643286 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7423661299) ^ 258 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_8070842779 : Nat.Prime 8070842779 := by
  apply lucas_primality 8070842779 (2 : ZMod 8070842779)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (22051483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (22051483, 1)] : List FactorBlock).map factorBlockValue).prod) = 8070842779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_twentyThreeU_22051483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8070842779) ^ 4035421389 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8070842779) ^ 2690280926 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8070842779) ^ 132308898 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8070842779) ^ 366 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_9397157443 : Nat.Prime 9397157443 := by
  apply lucas_primality 9397157443 (2 : ZMod 9397157443)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (157, 1), (243311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (157, 1), (243311, 1)] : List FactorBlock).map factorBlockValue).prod) = 9397157443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_t64_157
      · exact prime_twentyThreeU_243311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9397157443) ^ 4698578721 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 3132385814 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 229198962 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 59854506 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9397157443) ^ 38622 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_11570412613 : Nat.Prime 11570412613 := by
  apply lucas_primality 11570412613 (5 : ZMod 11570412613)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (87654641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (87654641, 1)] : List FactorBlock).map factorBlockValue).prod) = 11570412613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyThreeU_87654641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11570412613) ^ 5785206306 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11570412613) ^ 3856804204 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11570412613) ^ 1051855692 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11570412613) ^ 132 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13028721283 : Nat.Prime 13028721283 := by
  apply lucas_primality 13028721283 (2 : ZMod 13028721283)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (9915313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (9915313, 1)] : List FactorBlock).map factorBlockValue).prod) = 13028721283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_73
      · exact prime_twentyThreeU_9915313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13028721283) ^ 6514360641 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 4342907094 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 178475634 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13028721283) ^ 1314 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13187705449 : Nat.Prime 13187705449 := by
  apply lucas_primality 13187705449 (11 : ZMod 13187705449)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (677, 1), (811651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (677, 1), (811651, 1)] : List FactorBlock).map factorBlockValue).prod) = 13187705449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_677
      · exact prime_twentyThreeU_811651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 13187705449) ^ 6593852724 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 4395901816 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 19479624 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 13187705449) ^ 16248 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15117196799 : Nat.Prime 15117196799 := by
  apply lucas_primality 15117196799 (11 : ZMod 15117196799)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (29875883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (29875883, 1)] : List FactorBlock).map factorBlockValue).prod) = 15117196799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_twentyThreeU_29875883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 15117196799) ^ 7558598399 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 15117196799) ^ 1374290618 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 15117196799) ^ 657269426 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 15117196799) ^ 506 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15118640561 : Nat.Prime 15118640561 := by
  apply lucas_primality 15118640561 (3 : ZMod 15118640561)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (188983007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (188983007, 1)] : List FactorBlock).map factorBlockValue).prod) = 15118640561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_188983007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15118640561) ^ 7559320280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15118640561) ^ 3023728112 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15118640561) ^ 80 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_16744729277 : Nat.Prime 16744729277 := by
  apply lucas_primality 16744729277 (2 : ZMod 16744729277)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (380562029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (380562029, 1)] : List FactorBlock).map factorBlockValue).prod) = 16744729277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_twentyThreeU_380562029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16744729277) ^ 8372364638 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744729277) ^ 1522248116 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16744729277) ^ 44 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_18050932301 : Nat.Prime 18050932301 := by
  apply lucas_primality 18050932301 (2 : ZMod 18050932301)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (67, 1), (2694169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (67, 1), (2694169, 1)] : List FactorBlock).map factorBlockValue).prod) = 18050932301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_67
      · exact prime_twentyThreeU_2694169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18050932301) ^ 9025466150 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18050932301) ^ 3610186460 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18050932301) ^ 269416900 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18050932301) ^ 6700 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_25536840919 : Nat.Prime 25536840919 := by
  apply lucas_primality 25536840919 (7 : ZMod 25536840919)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4256140153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4256140153, 1)] : List FactorBlock).map factorBlockValue).prod) = 25536840919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_4256140153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 25536840919) ^ 12768420459 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 25536840919) ^ 8512280306 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 25536840919) ^ 6 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_26202573167 : Nat.Prime 26202573167 := by
  apply lucas_primality 26202573167 (7 : ZMod 26202573167)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (8297, 1), (20507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (8297, 1), (20507, 1)] : List FactorBlock).map factorBlockValue).prod) = 26202573167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_twentyThreeU_8297
      · exact prime_twentyThreeU_20507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26202573167) ^ 13101286583 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 26202573167) ^ 3743224738 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 26202573167) ^ 2382052106 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 26202573167) ^ 3158078 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 26202573167) ^ 1277738 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_27262846097 : Nat.Prime 27262846097 := by
  apply lucas_primality 27262846097 (3 : ZMod 27262846097)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1703927881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1703927881, 1)] : List FactorBlock).map factorBlockValue).prod) = 27262846097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_1703927881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 27262846097) ^ 13631423048 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 27262846097) ^ 16 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_29500037251 : Nat.Prime 29500037251 := by
  apply lucas_primality 29500037251 (14 : ZMod 29500037251)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (39333383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (39333383, 1)] : List FactorBlock).map factorBlockValue).prod) = 29500037251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_39333383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 29500037251) ^ 14750018625 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 29500037251) ^ 9833345750 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 29500037251) ^ 5900007450 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 29500037251) ^ 750 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_33733056821 : Nat.Prime 33733056821 := by
  apply lucas_primality 33733056821 (2 : ZMod 33733056821)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 2), (67, 1), (87107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 2), (67, 1), (87107, 1)] : List FactorBlock).map factorBlockValue).prod) = 33733056821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_67
      · exact prime_twentyThreeU_87107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33733056821) ^ 16866528410 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33733056821) ^ 6746611364 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33733056821) ^ 1984297460 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33733056821) ^ 503478460 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 33733056821) ^ 387260 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_53993183347 : Nat.Prime 53993183347 := by
  apply lucas_primality 53993183347 (2 : ZMod 53993183347)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11273, 1), (266089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11273, 1), (266089, 1)] : List FactorBlock).map factorBlockValue).prod) = 53993183347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_11273
      · exact prime_twentyThreeU_266089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53993183347) ^ 26996591673 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53993183347) ^ 17997727782 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53993183347) ^ 4789602 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 53993183347) ^ 202914 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_57355267721 : Nat.Prime 57355267721 := by
  apply lucas_primality 57355267721 (3 : ZMod 57355267721)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2903, 1), (493931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2903, 1), (493931, 1)] : List FactorBlock).map factorBlockValue).prod) = 57355267721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_2903
      · exact prime_twentyThreeU_493931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57355267721) ^ 28677633860 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 11471053544 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 19757240 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 57355267721) ^ 116120 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_71491695013 : Nat.Prime 71491695013 := by
  apply lucas_primality 71491695013 (2 : ZMod 71491695013)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (9109, 1), (72671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (9109, 1), (72671, 1)] : List FactorBlock).map factorBlockValue).prod) = 71491695013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_9109
      · exact prime_twentyThreeU_72671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71491695013) ^ 35745847506 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 23830565004 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 7848468 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 71491695013) ^ 983772 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_79699235591 : Nat.Prime 79699235591 := by
  apply lucas_primality 79699235591 (23 : ZMod 79699235591)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 2), (19, 1), (2482069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 2), (19, 1), (2482069, 1)] : List FactorBlock).map factorBlockValue).prod) = 79699235591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_twentyThreeU_2482069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 79699235591) ^ 39849617795 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 79699235591) ^ 15939847118 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 79699235591) ^ 6130710430 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 79699235591) ^ 4194696610 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (23 : ZMod 79699235591) ^ 32110 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_88920655909 : Nat.Prime 88920655909 := by
  apply lucas_primality 88920655909 (10 : ZMod 88920655909)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1489, 1), (710933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1489, 1), (710933, 1)] : List FactorBlock).map factorBlockValue).prod) = 88920655909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_1489
      · exact prime_twentyThreeU_710933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 88920655909) ^ 44460327954 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88920655909) ^ 29640218636 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88920655909) ^ 12702950844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88920655909) ^ 59718372 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 88920655909) ^ 125076 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_97926671179 : Nat.Prime 97926671179 := by
  apply lucas_primality 97926671179 (3 : ZMod 97926671179)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (43, 1), (337, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (43, 1), (337, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) = 97926671179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_43
      · exact prime_twentyThreeU_337
      · exact prime_twentyThreeU_53633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 97926671179) ^ 48963335589 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 32642223726 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 13989524454 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 2277364446 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 290583594 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 97926671179) ^ 1825866 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_106247777549 : Nat.Prime 106247777549 := by
  apply lucas_primality 106247777549 (2 : ZMod 106247777549)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (127090643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (127090643, 1)] : List FactorBlock).map factorBlockValue).prod) = 106247777549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_twentyThreeU_127090643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106247777549) ^ 53123888774 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 9658888868 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 5591988292 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 106247777549) ^ 836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_116778303307 : Nat.Prime 116778303307 := by
  apply lucas_primality 116778303307 (3 : ZMod 116778303307)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (9221, 1), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (9221, 1), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) = 116778303307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_9221
      · exact prime_twentyThreeU_100511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116778303307) ^ 58389151653 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 38926101102 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 16682614758 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 12664386 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 116778303307) ^ 1161846 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_133660878913 : Nat.Prime 133660878913 := by
  apply lucas_primality 133660878913 (15 : ZMod 133660878913)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11, 1), (73, 1), (288979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11, 1), (73, 1), (288979, 1)] : List FactorBlock).map factorBlockValue).prod) = 133660878913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_73
      · exact prime_twentyThreeU_288979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 133660878913) ^ 66830439456 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 44553626304 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 12150988992 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 1830970944 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (15 : ZMod 133660878913) ^ 462528 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_176510284939 : Nat.Prime 176510284939 := by
  apply lucas_primality 176510284939 (2 : ZMod 176510284939)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (167, 1), (439, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (167, 1), (439, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) = 176510284939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_167
      · exact prime_t64_439
      · exact prime_twentyThreeU_10289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 176510284939) ^ 88255142469 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 58836761646 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 13577714226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 1056947814 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 402073542 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 176510284939) ^ 17155242 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_285962179991 : Nat.Prime 285962179991 := by
  apply lucas_primality 285962179991 (11 : ZMod 285962179991)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (59, 1), (61, 1), (197, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (59, 1), (61, 1), (197, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 285962179991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_61
      · exact prime_t64_197
      · exact prime_t64_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 285962179991) ^ 142981089995 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 57192435998 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 5395512830 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 4846816610 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 4687904590 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 1451584670 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 285962179991) ^ 375771590 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_405435158291 : Nat.Prime 405435158291 := by
  apply lucas_primality 405435158291 (2 : ZMod 405435158291)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (461, 1), (87946889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (461, 1), (87946889, 1)] : List FactorBlock).map factorBlockValue).prod) = 405435158291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_461
      · exact prime_twentyThreeU_87946889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 405435158291) ^ 202717579145 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 405435158291) ^ 81087031658 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 405435158291) ^ 879468890 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 405435158291) ^ 4610 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_483499128269 : Nat.Prime 483499128269 := by
  apply lucas_primality 483499128269 (2 : ZMod 483499128269)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (9623, 1), (966233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (9623, 1), (966233, 1)] : List FactorBlock).map factorBlockValue).prod) = 483499128269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentyThreeU_9623
      · exact prime_twentyThreeU_966233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483499128269) ^ 241749564134 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483499128269) ^ 37192240636 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483499128269) ^ 50244116 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 483499128269) ^ 500396 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_617623095907 : Nat.Prime 617623095907 := by
  apply lucas_primality 617623095907 (3 : ZMod 617623095907)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (239, 1), (47855501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (239, 1), (47855501, 1)] : List FactorBlock).map factorBlockValue).prod) = 617623095907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_239
      · exact prime_twentyThreeU_47855501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 617623095907) ^ 308811547953 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 205874365302 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 2584197054 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 617623095907) ^ 12906 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_651827067131 : Nat.Prime 651827067131 := by
  apply lucas_primality 651827067131 (6 : ZMod 651827067131)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (3019, 1), (84011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (3019, 1), (84011, 1)] : List FactorBlock).map factorBlockValue).prod) = 651827067131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_257
      · exact prime_twentyThreeU_3019
      · exact prime_twentyThreeU_84011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 651827067131) ^ 325913533565 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 651827067131) ^ 130365413426 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 651827067131) ^ 2536292090 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 651827067131) ^ 215908270 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 651827067131) ^ 7758830 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_766105227571 : Nat.Prime 766105227571 := by
  apply lucas_primality 766105227571 (3 : ZMod 766105227571)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (25536840919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (25536840919, 1)] : List FactorBlock).map factorBlockValue).prod) = 766105227571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_25536840919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 766105227571) ^ 383052613785 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 255368409190 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 153221045514 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 766105227571) ^ 30 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_834551915881 : Nat.Prime 834551915881 := by
  apply lucas_primality 834551915881 (11 : ZMod 834551915881)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (83, 1), (151, 1), (523, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (83, 1), (151, 1), (523, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 834551915881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_83
      · exact prime_twentyThreeU_151
      · exact prime_twentyThreeU_523
      · exact prime_t64_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 834551915881) ^ 417275957940 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 278183971960 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 166910383176 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 10054842360 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 5526833880 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 1595701560 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 834551915881) ^ 786571080 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_840939634417 : Nat.Prime 840939634417 := by
  apply lucas_primality 840939634417 (10 : ZMod 840939634417)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (23369, 1), (107099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (23369, 1), (107099, 1)] : List FactorBlock).map factorBlockValue).prod) = 840939634417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_23369
      · exact prime_twentyThreeU_107099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 840939634417) ^ 420469817208 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 280313211472 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 120134233488 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 35985264 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 840939634417) ^ 7851984 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_926949530179 : Nat.Prime 926949530179 := by
  apply lucas_primality 926949530179 (2 : ZMod 926949530179)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (319858361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (319858361, 1)] : List FactorBlock).map factorBlockValue).prod) = 926949530179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_twentyThreeU_319858361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 926949530179) ^ 463474765089 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 926949530179) ^ 308983176726 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 926949530179) ^ 132421361454 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 926949530179) ^ 40302153486 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 926949530179) ^ 2898 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1026385466377 : Nat.Prime 1026385466377 := by
  apply lucas_primality 1026385466377 (5 : ZMod 1026385466377)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (163, 1), (257, 1), (53731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (163, 1), (257, 1), (53731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026385466377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_163
      · exact prime_twentyThreeU_257
      · exact prime_twentyThreeU_53731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1026385466377) ^ 513192733188 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 342128488792 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 54020287704 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 6296843352 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 3993717768 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1026385466377) ^ 19102296 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1166782634291 : Nat.Prime 1166782634291 := by
  apply lucas_primality 1166782634291 (2 : ZMod 1166782634291)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (1282178719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (1282178719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166782634291 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_twentyThreeU_1282178719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1166782634291) ^ 583391317145 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166782634291) ^ 233356526858 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166782634291) ^ 166683233470 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166782634291) ^ 89752510330 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166782634291) ^ 910 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1204531986989 : Nat.Prime 1204531986989 := by
  apply lucas_primality 1204531986989 (2 : ZMod 1204531986989)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (827, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (827, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1204531986989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_twentyThreeU_827
      · exact prime_twentyThreeU_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1204531986989) ^ 602265993494 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 109502907908 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 70854822764 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 52370955956 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 38855870548 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 1456507844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204531986989) ^ 441058948 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1354488340669 : Nat.Prime 1354488340669 := by
  apply lucas_primality 1354488340669 (2 : ZMod 1354488340669)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (84047, 1), (1342987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (84047, 1), (1342987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1354488340669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_84047
      · exact prime_twentyThreeU_1342987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1354488340669) ^ 677244170334 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1354488340669) ^ 451496113556 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1354488340669) ^ 16115844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1354488340669) ^ 1008564 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1602309601687 : Nat.Prime 1602309601687 := by
  apply lucas_primality 1602309601687 (3 : ZMod 1602309601687)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (1061, 1), (1259, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (1061, 1), (1259, 1), (6449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1602309601687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_1061
      · exact prime_twentyThreeU_1259
      · exact prime_twentyThreeU_6449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1602309601687) ^ 801154800843 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 534103200562 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 51687406506 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 1510188126 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 1272684354 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1602309601687) ^ 248458614 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1726174584847 : Nat.Prime 1726174584847 := by
  apply lucas_primality 1726174584847 (5 : ZMod 1726174584847)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (2591853731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (2591853731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1726174584847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_twentyThreeU_2591853731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1726174584847) ^ 863087292423 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1726174584847) ^ 575391528282 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1726174584847) ^ 46653367158 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1726174584847) ^ 666 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2756990764841 : Nat.Prime 2756990764841 := by
  apply lucas_primality 2756990764841 (3 : ZMod 2756990764841)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (557, 1), (9518681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (557, 1), (9518681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2756990764841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyThreeU_557
      · exact prime_twentyThreeU_9518681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2756990764841) ^ 1378495382420 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 551398152968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 212076212680 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 4949714120 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2756990764841) ^ 289640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2803786716131 : Nat.Prime 2803786716131 := by
  apply lucas_primality 2803786716131 (2 : ZMod 2803786716131)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (104003, 1), (2695871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (104003, 1), (2695871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2803786716131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_104003
      · exact prime_twentyThreeU_2695871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2803786716131) ^ 1401893358065 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2803786716131) ^ 560757343226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2803786716131) ^ 26958710 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2803786716131) ^ 1040030 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3895148684197 : Nat.Prime 3895148684197 := by
  apply lucas_primality 3895148684197 (5 : ZMod 3895148684197)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (19, 1), (4350391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (17, 1), (19, 1), (4350391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3895148684197 - 1 by
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
      · exact prime_t64_19
      · exact prime_twentyThreeU_4350391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3895148684197) ^ 1947574342098 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 1298382894732 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 556449812028 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 354104425836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 229126393188 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 205007825484 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3895148684197) ^ 895356 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_4018917173657 : Nat.Prime 4018917173657 := by
  apply lucas_primality 4018917173657 (3 : ZMod 4018917173657)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (17, 1), (9413, 1), (40771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (17, 1), (9413, 1), (40771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4018917173657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_twentyThreeU_9413
      · exact prime_twentyThreeU_40771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4018917173657) ^ 2009458586828 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 574131024808 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 365356106696 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 236406892568 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 426953912 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4018917173657) ^ 98572936 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_5055654984467 : Nat.Prime 5055654984467 := by
  apply lucas_primality 5055654984467 (2 : ZMod 5055654984467)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (7243058717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (7243058717, 1)] : List FactorBlock).map factorBlockValue).prod) = 5055654984467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_349
      · exact prime_twentyThreeU_7243058717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5055654984467) ^ 2527827492233 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055654984467) ^ 14486117434 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 5055654984467) ^ 698 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_6136007748209 : Nat.Prime 6136007748209 := by
  apply lucas_primality 6136007748209 (3 : ZMod 6136007748209)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (29500037251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (29500037251, 1)] : List FactorBlock).map factorBlockValue).prod) = 6136007748209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentyThreeU_29500037251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6136007748209) ^ 3068003874104 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6136007748209) ^ 472000596016 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6136007748209) ^ 208 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_6614481846563 : Nat.Prime 6614481846563 := by
  apply lucas_primality 6614481846563 (2 : ZMod 6614481846563)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57719, 1), (57298999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57719, 1), (57298999, 1)] : List FactorBlock).map factorBlockValue).prod) = 6614481846563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_57719
      · exact prime_twentyThreeU_57298999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6614481846563) ^ 3307240923281 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614481846563) ^ 114597998 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 6614481846563) ^ 115438 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7256947469281 : Nat.Prime 7256947469281 := by
  apply lucas_primality 7256947469281 (14 : ZMod 7256947469281)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (15118640561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (15118640561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7256947469281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_15118640561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 7256947469281) ^ 3628473734640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 2418982489760 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 1451389493856 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (14 : ZMod 7256947469281) ^ 480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7402100472937 : Nat.Prime 7402100472937 := by
  apply lucas_primality 7402100472937 (5 : ZMod 7402100472937)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (13, 1), (149, 1), (5897261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (13, 1), (149, 1), (5897261, 1)] : List FactorBlock).map factorBlockValue).prod) = 7402100472937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_149
      · exact prime_twentyThreeU_5897261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7402100472937) ^ 3701050236468 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7402100472937) ^ 2467366824312 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7402100472937) ^ 569392344072 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7402100472937) ^ 49678526664 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7402100472937) ^ 1255176 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7538507136859 : Nat.Prime 7538507136859 := by
  apply lucas_primality 7538507136859 (2 : ZMod 7538507136859)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1933, 1), (649983371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1933, 1), (649983371, 1)] : List FactorBlock).map factorBlockValue).prod) = 7538507136859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_1933
      · exact prime_twentyThreeU_649983371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7538507136859) ^ 3769253568429 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 2512835712286 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 3899900226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7538507136859) ^ 11598 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_8488118303299 : Nat.Prime 8488118303299 := by
  apply lucas_primality 8488118303299 (2 : ZMod 8488118303299)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (103, 1), (1526091029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (103, 1), (1526091029, 1)] : List FactorBlock).map factorBlockValue).prod) = 8488118303299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_103
      · exact prime_twentyThreeU_1526091029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8488118303299) ^ 4244059151649 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8488118303299) ^ 2829372767766 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8488118303299) ^ 82408915566 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8488118303299) ^ 5562 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_8668303629341 : Nat.Prime 8668303629341 := by
  apply lucas_primality 8668303629341 (2 : ZMod 8668303629341)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (761, 1), (1051, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (761, 1), (1051, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) = 8668303629341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_t64_761
      · exact prime_t64_1051
      · exact prime_twentyThreeU_13217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8668303629341) ^ 4334151814670 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8668303629341) ^ 1733660725868 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8668303629341) ^ 211422039740 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8668303629341) ^ 11390674940 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8668303629341) ^ 8247672340 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8668303629341) ^ 655845020 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_9225270165289 : Nat.Prime 9225270165289 := by
  apply lucas_primality 9225270165289 (7 : ZMod 9225270165289)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (574913, 1), (668599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (574913, 1), (668599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9225270165289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_574913
      · exact prime_twentyThreeU_668599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9225270165289) ^ 4612635082644 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 3075090055096 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 16046376 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9225270165289) ^ 13797912 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_11003914253261 : Nat.Prime 11003914253261 := by
  apply lucas_primality 11003914253261 (3 : ZMod 11003914253261)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1451, 1), (6311, 1), (60083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1451, 1), (6311, 1), (60083, 1)] : List FactorBlock).map factorBlockValue).prod) = 11003914253261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_1451
      · exact prime_twentyThreeU_6311
      · exact prime_twentyThreeU_60083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11003914253261) ^ 5501957126630 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 2200782850652 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 7583676260 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 1743608660 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11003914253261) ^ 183145220 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_12973925065313 : Nat.Prime 12973925065313 := by
  apply lucas_primality 12973925065313 (3 : ZMod 12973925065313)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (405435158291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (405435158291, 1)] : List FactorBlock).map factorBlockValue).prod) = 12973925065313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_405435158291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 12973925065313) ^ 6486962532656 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 12973925065313) ^ 32 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13048881437167 : Nat.Prime 13048881437167 := by
  apply lucas_primality 13048881437167 (3 : ZMod 13048881437167)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (26202573167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (26202573167, 1)] : List FactorBlock).map factorBlockValue).prod) = 13048881437167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_twentyThreeU_26202573167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13048881437167) ^ 6524440718583 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13048881437167) ^ 4349627145722 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13048881437167) ^ 157215439002 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13048881437167) ^ 498 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13455034150673 : Nat.Prime 13455034150673 := by
  apply lucas_primality 13455034150673 (3 : ZMod 13455034150673)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (840939634417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (840939634417, 1)] : List FactorBlock).map factorBlockValue).prod) = 13455034150673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_840939634417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13455034150673) ^ 6727517075336 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13455034150673) ^ 16 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13938717533443 : Nat.Prime 13938717533443 := by
  apply lucas_primality 13938717533443 (2 : ZMod 13938717533443)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (61, 1), (12841, 1), (228139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (61, 1), (12841, 1), (228139, 1)] : List FactorBlock).map factorBlockValue).prod) = 13938717533443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_61
      · exact prime_twentyThreeU_12841
      · exact prime_twentyThreeU_228139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13938717533443) ^ 6969358766721 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 4646239177814 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 1072209041034 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 228503566122 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 1085485362 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13938717533443) ^ 61097478 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15207691149977 : Nat.Prime 15207691149977 := by
  apply lucas_primality 15207691149977 (3 : ZMod 15207691149977)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (47, 1), (3111229777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (47, 1), (3111229777, 1)] : List FactorBlock).map factorBlockValue).prod) = 15207691149977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_47
      · exact prime_twentyThreeU_3111229777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15207691149977) ^ 7603845574988 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15207691149977) ^ 1169822396152 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15207691149977) ^ 323567896808 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15207691149977) ^ 4888 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_15537659940391 : Nat.Prime 15537659940391 := by
  apply lucas_primality 15537659940391 (6 : ZMod 15537659940391)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (47, 1), (2399, 1), (34537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (47, 1), (2399, 1), (34537, 1)] : List FactorBlock).map factorBlockValue).prod) = 15537659940391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_47
      · exact prime_twentyThreeU_2399
      · exact prime_twentyThreeU_34537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15537659940391) ^ 7768829970195 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 5179219980130 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 3107531988078 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 2219665705770 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 817771575810 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 330588509370 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 6476723610 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 15537659940391) ^ 449884470 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_16027271091163 : Nat.Prime 16027271091163 := by
  apply lucas_primality 16027271091163 (2 : ZMod 16027271091163)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (491, 1), (604483333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (491, 1), (604483333, 1)] : List FactorBlock).map factorBlockValue).prod) = 16027271091163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_491
      · exact prime_twentyThreeU_604483333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16027271091163) ^ 8013635545581 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 5342423697054 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 32642099982 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 16027271091163) ^ 26514 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_16116755127691 : Nat.Prime 16116755127691 := by
  apply lucas_primality 16116755127691 (3 : ZMod 16116755127691)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1213, 1), (63269953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1213, 1), (63269953, 1)] : List FactorBlock).map factorBlockValue).prod) = 16116755127691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_1213
      · exact prime_twentyThreeU_63269953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16116755127691) ^ 8058377563845 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 5372251709230 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 3223351025538 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 2302393589670 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 13286690130 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 16116755127691) ^ 254730 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_21049165425103 : Nat.Prime 21049165425103 := by
  apply lucas_primality 21049165425103 (6 : ZMod 21049165425103)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359483, 1), (9758999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359483, 1), (9758999, 1)] : List FactorBlock).map factorBlockValue).prod) = 21049165425103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_359483
      · exact prime_twentyThreeU_9758999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 21049165425103) ^ 10524582712551 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21049165425103) ^ 7016388475034 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21049165425103) ^ 58553994 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 21049165425103) ^ 2156898 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_26870600560577 : Nat.Prime 26870600560577 := by
  apply lucas_primality 26870600560577 (3 : ZMod 26870600560577)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (983, 1), (20563, 1), (20771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (983, 1), (20563, 1), (20771, 1)] : List FactorBlock).map factorBlockValue).prod) = 26870600560577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_983
      · exact prime_twentyThreeU_20563
      · exact prime_twentyThreeU_20771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26870600560577) ^ 13435300280288 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26870600560577) ^ 27335300672 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26870600560577) ^ 1306745152 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 26870600560577) ^ 1293659456 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_27648080720861 : Nat.Prime 27648080720861 := by
  apply lucas_primality 27648080720861 (2 : ZMod 27648080720861)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (709, 1), (3011, 1), (647557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (709, 1), (3011, 1), (647557, 1)] : List FactorBlock).map factorBlockValue).prod) = 27648080720861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_709
      · exact prime_twentyThreeU_3011
      · exact prime_twentyThreeU_647557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27648080720861) ^ 13824040360430 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 5529616144172 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 38995882540 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 9182358260 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27648080720861) ^ 42695980 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_32676686592311 : Nat.Prime 32676686592311 := by
  apply lucas_primality 32676686592311 (11 : ZMod 32676686592311)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (79699235591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (79699235591, 1)] : List FactorBlock).map factorBlockValue).prod) = 32676686592311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_twentyThreeU_79699235591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 32676686592311) ^ 16338343296155 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 32676686592311) ^ 6535337318462 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 32676686592311) ^ 796992355910 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 32676686592311) ^ 410 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_39738982943393 : Nat.Prime 39738982943393 := by
  apply lucas_primality 39738982943393 (3 : ZMod 39738982943393)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (53993183347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (53993183347, 1)] : List FactorBlock).map factorBlockValue).prod) = 39738982943393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyThreeU_53993183347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 39738982943393) ^ 19869491471696 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39738982943393) ^ 1727781867104 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 39738982943393) ^ 736 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_52332132488113 : Nat.Prime 52332132488113 := by
  apply lucas_primality 52332132488113 (5 : ZMod 52332132488113)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (97, 1), (3746573059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (97, 1), (3746573059, 1)] : List FactorBlock).map factorBlockValue).prod) = 52332132488113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_97
      · exact prime_twentyThreeU_3746573059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52332132488113) ^ 26166066244056 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 17444044162704 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 539506520496 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 52332132488113) ^ 13968 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_59251137966073 : Nat.Prime 59251137966073 := by
  apply lucas_primality 59251137966073 (10 : ZMod 59251137966073)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (331, 1), (63748739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (331, 1), (63748739, 1)] : List FactorBlock).map factorBlockValue).prod) = 59251137966073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyThreeU_331
      · exact prime_twentyThreeU_63748739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 59251137966073) ^ 29625568983036 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 59251137966073) ^ 19750379322024 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 59251137966073) ^ 4557779843544 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 59251137966073) ^ 179006459112 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 59251137966073) ^ 929448 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_66502848765757 : Nat.Prime 66502848765757 := by
  apply lucas_primality 66502848765757 (2 : ZMod 66502848765757)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23369, 1), (18242129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23369, 1), (18242129, 1)] : List FactorBlock).map factorBlockValue).prod) = 66502848765757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyThreeU_23369
      · exact prime_twentyThreeU_18242129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66502848765757) ^ 33251424382878 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 66502848765757) ^ 22167616255252 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 66502848765757) ^ 5115603751212 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 66502848765757) ^ 2845772124 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 66502848765757) ^ 3645564 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_94256492157427 : Nat.Prime 94256492157427 := by
  apply lucas_primality 94256492157427 (2 : ZMod 94256492157427)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (176510284939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (176510284939, 1)] : List FactorBlock).map factorBlockValue).prod) = 94256492157427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_twentyThreeU_176510284939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94256492157427) ^ 47128246078713 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 31418830719142 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 1059061709634 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94256492157427) ^ 534 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_107556384046561 : Nat.Prime 107556384046561 := by
  apply lucas_primality 107556384046561 (13 : ZMod 107556384046561)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (19, 1), (41, 1), (287645443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (19, 1), (41, 1), (287645443, 1)] : List FactorBlock).map factorBlockValue).prod) = 107556384046561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_t64_41
      · exact prime_twentyThreeU_287645443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 107556384046561) ^ 53778192023280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 35852128015520 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 21511276809312 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 5660862318240 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 2623326440160 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 107556384046561) ^ 373920 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_107759576947691 : Nat.Prime 107759576947691 := by
  apply lucas_primality 107759576947691 (6 : ZMod 107759576947691)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (1049, 1), (144684511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (1049, 1), (144684511, 1)] : List FactorBlock).map factorBlockValue).prod) = 107759576947691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_71
      · exact prime_twentyThreeU_1049
      · exact prime_twentyThreeU_144684511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 107759576947691) ^ 53879788473845 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 107759576947691) ^ 21551915389538 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 107759576947691) ^ 1517740520390 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 107759576947691) ^ 102726002810 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 107759576947691) ^ 744790 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_123538110311453 : Nat.Prime 123538110311453 := by
  apply lucas_primality 123538110311453 (2 : ZMod 123538110311453)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (66593, 1), (463780391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (66593, 1), (463780391, 1)] : List FactorBlock).map factorBlockValue).prod) = 123538110311453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_66593
      · exact prime_twentyThreeU_463780391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 123538110311453) ^ 61769055155726 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 123538110311453) ^ 1855121564 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 123538110311453) ^ 266372 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_135548253744649 : Nat.Prime 135548253744649 := by
  apply lucas_primality 135548253744649 (13 : ZMod 135548253744649)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (71491695013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (71491695013, 1)] : List FactorBlock).map factorBlockValue).prod) = 135548253744649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_79
      · exact prime_twentyThreeU_71491695013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 135548253744649) ^ 67774126872324 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 45182751248216 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 1715800680312 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 135548253744649) ^ 1896 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_193133325806587 : Nat.Prime 193133325806587 := by
  apply lucas_primality 193133325806587 (2 : ZMod 193133325806587)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (409, 1), (2384892023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (409, 1), (2384892023, 1)] : List FactorBlock).map factorBlockValue).prod) = 193133325806587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_409
      · exact prime_twentyThreeU_2384892023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 193133325806587) ^ 96566662903293 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 193133325806587) ^ 64377775268862 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 193133325806587) ^ 17557575073326 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 193133325806587) ^ 472208620554 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 193133325806587) ^ 80982 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_196741102020989 : Nat.Prime 196741102020989 := by
  apply lucas_primality 196741102020989 (2 : ZMod 196741102020989)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1109, 1), (6335859269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1109, 1), (6335859269, 1)] : List FactorBlock).map factorBlockValue).prod) = 196741102020989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_1109
      · exact prime_twentyThreeU_6335859269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 196741102020989) ^ 98370551010494 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 28105871717284 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 177404059532 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 196741102020989) ^ 31052 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_209328529952453 : Nat.Prime 209328529952453 := by
  apply lucas_primality 209328529952453 (2 : ZMod 209328529952453)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52332132488113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52332132488113, 1)] : List FactorBlock).map factorBlockValue).prod) = 209328529952453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_52332132488113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 209328529952453) ^ 104664264976226 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 209328529952453) ^ 4 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_334529220802633 : Nat.Prime 334529220802633 := by
  apply lucas_primality 334529220802633 (5 : ZMod 334529220802633)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13938717533443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13938717533443, 1)] : List FactorBlock).map factorBlockValue).prod) = 334529220802633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_13938717533443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 334529220802633) ^ 167264610401316 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 334529220802633) ^ 111509740267544 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 334529220802633) ^ 24 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_380053619276029 : Nat.Prime 380053619276029 := by
  apply lucas_primality 380053619276029 (6 : ZMod 380053619276029)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229699, 1), (137881031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229699, 1), (137881031, 1)] : List FactorBlock).map factorBlockValue).prod) = 380053619276029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_229699
      · exact prime_twentyThreeU_137881031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 380053619276029) ^ 190026809638014 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 126684539758676 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 1654572372 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 380053619276029) ^ 2756388 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_491407321771651 : Nat.Prime 491407321771651 := by
  apply lucas_primality 491407321771651 (2 : ZMod 491407321771651)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (991, 1), (4349, 1), (760129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (991, 1), (4349, 1), (760129, 1)] : List FactorBlock).map factorBlockValue).prod) = 491407321771651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_991
      · exact prime_twentyThreeU_4349
      · exact prime_twentyThreeU_760129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 491407321771651) ^ 245703660885825 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 491407321771651) ^ 163802440590550 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 491407321771651) ^ 98281464354330 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 491407321771651) ^ 495870153150 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 491407321771651) ^ 112993175850 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 491407321771651) ^ 646478850 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_520826605545199 : Nat.Prime 520826605545199 := by
  apply lucas_primality 520826605545199 (3 : ZMod 520826605545199)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (43, 1), (106247777549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (43, 1), (106247777549, 1)] : List FactorBlock).map factorBlockValue).prod) = 520826605545199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_t64_43
      · exact prime_twentyThreeU_106247777549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 520826605545199) ^ 260413302772599 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 173608868515066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 27411926607642 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 12112246640586 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 520826605545199) ^ 4902 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_562934174401163 : Nat.Prime 562934174401163 := by
  apply lucas_primality 562934174401163 (2 : ZMod 562934174401163)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (433, 1), (15117196799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (433, 1), (15117196799, 1)] : List FactorBlock).map factorBlockValue).prod) = 562934174401163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_t64_433
      · exact prime_twentyThreeU_15117196799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 562934174401163) ^ 281467087200581 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 562934174401163) ^ 13091492427934 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 562934174401163) ^ 1300078924714 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 562934174401163) ^ 37238 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_644995937440229 : Nat.Prime 644995937440229 := by
  apply lucas_primality 644995937440229 (2 : ZMod 644995937440229)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (1209388547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (23, 1), (31, 1), (1209388547, 1)] : List FactorBlock).map factorBlockValue).prod) = 644995937440229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_twentyThreeU_1209388547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 644995937440229) ^ 322497968720114 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 58635994312748 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 37940937496484 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 28043301627836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 20806320562588 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 644995937440229) ^ 533324 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_792963000799919 : Nat.Prime 792963000799919 := by
  apply lucas_primality 792963000799919 (11 : ZMod 792963000799919)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (739, 1), (103333, 1), (399389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (739, 1), (103333, 1), (399389, 1)] : List FactorBlock).map factorBlockValue).prod) = 792963000799919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_twentyThreeU_739
      · exact prime_twentyThreeU_103333
      · exact prime_twentyThreeU_399389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 792963000799919) ^ 396481500399959 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 60997153907686 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 1073021651962 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 7673860246 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 792963000799919) ^ 1985440262 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1250088974921609 : Nat.Prime 1250088974921609 := by
  apply lucas_primality 1250088974921609 (3 : ZMod 1250088974921609)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (41, 1), (13187705449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (41, 1), (13187705449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1250088974921609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_41
      · exact prime_twentyThreeU_13187705449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1250088974921609) ^ 625044487460804 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 73534645583624 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 30489974998088 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1250088974921609) ^ 94792 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1384920715659853 : Nat.Prime 1384920715659853 := by
  apply lucas_primality 1384920715659853 (5 : ZMod 1384920715659853)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (51479, 1), (13924759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (51479, 1), (13924759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1384920715659853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_twentyThreeU_51479
      · exact prime_twentyThreeU_13924759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1384920715659853) ^ 692460357829926 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1384920715659853) ^ 461640238553284 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1384920715659853) ^ 197845816522836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1384920715659853) ^ 60213944159124 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1384920715659853) ^ 26902634388 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1384920715659853) ^ 99457428 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1473705342963913 : Nat.Prime 1473705342963913 := by
  apply lucas_primality 1473705342963913 (5 : ZMod 1473705342963913)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (127, 1), (483499128269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (127, 1), (483499128269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1473705342963913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_127
      · exact prime_twentyThreeU_483499128269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1473705342963913) ^ 736852671481956 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1473705342963913) ^ 491235114321304 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1473705342963913) ^ 11603979078456 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1473705342963913) ^ 3048 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1520214477104117 : Nat.Prime 1520214477104117 := by
  apply lucas_primality 1520214477104117 (2 : ZMod 1520214477104117)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (380053619276029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (380053619276029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1520214477104117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_380053619276029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1520214477104117) ^ 760107238552058 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1520214477104117) ^ 4 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1530024826764883 : Nat.Prime 1530024826764883 := by
  apply lucas_primality 1530024826764883 (2 : ZMod 1530024826764883)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (431, 1), (72227, 1), (1170233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (431, 1), (72227, 1), (1170233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530024826764883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_431
      · exact prime_twentyThreeU_72227
      · exact prime_twentyThreeU_1170233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1530024826764883) ^ 765012413382441 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 510008275588294 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 218574975252126 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 3549941593422 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 21183557766 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530024826764883) ^ 1307453154 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1585926001599839 : Nat.Prime 1585926001599839 := by
  apply lucas_primality 1585926001599839 (7 : ZMod 1585926001599839)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (792963000799919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (792963000799919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585926001599839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_792963000799919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 1585926001599839) ^ 792963000799919 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1585926001599839) ^ 2 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2043742075411279 : Nat.Prime 2043742075411279 := by
  apply lucas_primality 2043742075411279 (3 : ZMod 2043742075411279)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (41, 1), (331, 1), (4919, 1), (463867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (41, 1), (331, 1), (4919, 1), (463867, 1)] : List FactorBlock).map factorBlockValue).prod) = 2043742075411279 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_twentyThreeU_331
      · exact prime_twentyThreeU_4919
      · exact prime_twentyThreeU_463867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2043742075411279) ^ 1021871037705639 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 681247358470426 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 185794734128298 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 49847367692958 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 6174447357738 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 415479177762 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2043742075411279) ^ 4405879434 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2754375428293847 : Nat.Prime 2754375428293847 := by
  apply lucas_primality 2754375428293847 (5 : ZMod 2754375428293847)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (196741102020989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (196741102020989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754375428293847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_196741102020989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2754375428293847) ^ 1377187714146923 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2754375428293847) ^ 393482204041978 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2754375428293847) ^ 14 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_4418040956711281 : Nat.Prime 4418040956711281 := by
  apply lucas_primality 4418040956711281 (29 : ZMod 4418040956711281)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (2014897, 1), (9136201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (2014897, 1), (9136201, 1)] : List FactorBlock).map factorBlockValue).prod) = 4418040956711281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_2014897
      · exact prime_twentyThreeU_9136201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 4418040956711281) ^ 2209020478355640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 4418040956711281) ^ 1472680318903760 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 4418040956711281) ^ 883608191342256 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 4418040956711281) ^ 2192688240 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (29 : ZMod 4418040956711281) ^ 483575280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7394023845594961 : Nat.Prime 7394023845594961 := by
  apply lucas_primality 7394023845594961 (62 : ZMod 7394023845594961)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (175663, 1), (25054819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (175663, 1), (25054819, 1)] : List FactorBlock).map factorBlockValue).prod) = 7394023845594961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_175663
      · exact prime_twentyThreeU_25054819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (62 : ZMod 7394023845594961) ^ 3697011922797480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (62 : ZMod 7394023845594961) ^ 2464674615198320 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (62 : ZMod 7394023845594961) ^ 1478804769118992 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (62 : ZMod 7394023845594961) ^ 1056289120799280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (62 : ZMod 7394023845594961) ^ 42092095920 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (62 : ZMod 7394023845594961) ^ 295113840 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_12987266597964433 : Nat.Prime 12987266597964433 := by
  apply lucas_primality 12987266597964433 (5 : ZMod 12987266597964433)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (41, 1), (1879, 1), (2143, 1), (546289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (41, 1), (1879, 1), (2143, 1), (546289, 1)] : List FactorBlock).map factorBlockValue).prod) = 12987266597964433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_twentyThreeU_1879
      · exact prime_twentyThreeU_2143
      · exact prime_twentyThreeU_546289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12987266597964433) ^ 6493633298982216 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 4329088865988144 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 316762599950352 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 6911797018608 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 6060320391024 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 12987266597964433) ^ 23773619088 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_41716798374222793 : Nat.Prime 41716798374222793 := by
  apply lucas_primality 41716798374222793 (5 : ZMod 41716798374222793)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (193133325806587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (193133325806587, 1)] : List FactorBlock).map factorBlockValue).prod) = 41716798374222793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_193133325806587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41716798374222793) ^ 20858399187111396 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 41716798374222793) ^ 13905599458074264 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 41716798374222793) ^ 216 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_52723584966097631 : Nat.Prime 52723584966097631 := by
  apply lucas_primality 52723584966097631 (11 : ZMod 52723584966097631)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (4661323, 1), (87006637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (4661323, 1), (87006637, 1)] : List FactorBlock).map factorBlockValue).prod) = 52723584966097631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyThreeU_4661323
      · exact prime_twentyThreeU_87006637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 52723584966097631) ^ 26361792483048815 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 10544716993219526 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 4055660382007510 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 11310862810 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 52723584966097631) ^ 605971990 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_64792065289942223 : Nat.Prime 64792065289942223 := by
  apply lucas_primality 64792065289942223 (5 : ZMod 64792065289942223)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (135548253744649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (135548253744649, 1)] : List FactorBlock).map factorBlockValue).prod) = 64792065289942223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_239
      · exact prime_twentyThreeU_135548253744649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64792065289942223) ^ 32396032644971111 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64792065289942223) ^ 271096507489298 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64792065289942223) ^ 478 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_89253755690860679 : Nat.Prime 89253755690860679 := by
  apply lucas_primality 89253755690860679 (7 : ZMod 89253755690860679)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (39738982943393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (39738982943393, 1)] : List FactorBlock).map factorBlockValue).prod) = 89253755690860679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_1123
      · exact prime_twentyThreeU_39738982943393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 89253755690860679) ^ 44626877845430339 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 89253755690860679) ^ 79477965886786 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 89253755690860679) ^ 2246 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_95033458984338893 : Nat.Prime 95033458984338893 := by
  apply lucas_primality 95033458984338893 (2 : ZMod 95033458984338893)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (349931, 1), (859423127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (349931, 1), (859423127, 1)] : List FactorBlock).map factorBlockValue).prod) = 95033458984338893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_twentyThreeU_349931
      · exact prime_twentyThreeU_859423127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95033458984338893) ^ 47516729492169446 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 95033458984338893) ^ 1202955177016948 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 95033458984338893) ^ 271577708132 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 95033458984338893) ^ 110578196 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_102955693875907123 : Nat.Prime 102955693875907123 := by
  apply lucas_primality 102955693875907123 (3 : ZMod 102955693875907123)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (622603, 1), (540402979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (622603, 1), (540402979, 1)] : List FactorBlock).map factorBlockValue).prod) = 102955693875907123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_twentyThreeU_622603
      · exact prime_twentyThreeU_540402979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102955693875907123) ^ 51477846937953561 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 34318564625302374 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 6056217286818066 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 165363311574 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 102955693875907123) ^ 190516518 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_267651688908085609 : Nat.Prime 267651688908085609 := by
  apply lucas_primality 267651688908085609 (22 : ZMod 267651688908085609)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (223, 1), (176951, 1), (40374097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (223, 1), (176951, 1), (40374097, 1)] : List FactorBlock).map factorBlockValue).prod) = 267651688908085609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_223
      · exact prime_twentyThreeU_176951
      · exact prime_twentyThreeU_40374097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 267651688908085609) ^ 133825844454042804 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 267651688908085609) ^ 89217229636028536 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 267651688908085609) ^ 38235955558297944 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 267651688908085609) ^ 1200231788825496 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 267651688908085609) ^ 1512575170008 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 267651688908085609) ^ 6629292264 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_270328603841520479 : Nat.Prime 270328603841520479 := by
  apply lucas_primality 270328603841520479 (13 : ZMod 270328603841520479)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9679, 1), (149323, 1), (93520067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9679, 1), (149323, 1), (93520067, 1)] : List FactorBlock).map factorBlockValue).prod) = 270328603841520479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_9679
      · exact prime_twentyThreeU_149323
      · exact prime_twentyThreeU_93520067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 270328603841520479) ^ 135164301920760239 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 27929393929282 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 1810361456986 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 270328603841520479) ^ 2890594634 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_278207824421392157 : Nat.Prime 278207824421392157 := by
  apply lucas_primality 278207824421392157 (2 : ZMod 278207824421392157)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (563, 1), (123538110311453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (563, 1), (123538110311453, 1)] : List FactorBlock).map factorBlockValue).prod) = 278207824421392157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_563
      · exact prime_twentyThreeU_123538110311453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 278207824421392157) ^ 139103912210696078 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 278207824421392157) ^ 494152441245812 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 278207824421392157) ^ 2252 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_281004545474211721 : Nat.Prime 281004545474211721 := by
  apply lucas_primality 281004545474211721 (11 : ZMod 281004545474211721)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (334529220802633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (334529220802633, 1)] : List FactorBlock).map factorBlockValue).prod) = 281004545474211721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_334529220802633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 281004545474211721) ^ 140502272737105860 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 93668181824737240 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 56200909094842344 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 40143506496315960 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 281004545474211721) ^ 840 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_284473926037278847 : Nat.Prime 284473926037278847 := by
  apply lucas_primality 284473926037278847 (5 : ZMod 284473926037278847)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (61, 1), (2936993, 1), (8019449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (61, 1), (2936993, 1), (8019449, 1)] : List FactorBlock).map factorBlockValue).prod) = 284473926037278847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_61
      · exact prime_twentyThreeU_2936993
      · exact prime_twentyThreeU_8019449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 284473926037278847) ^ 142236963018639423 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284473926037278847) ^ 94824642012426282 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284473926037278847) ^ 25861266003388986 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284473926037278847) ^ 4663506984217686 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284473926037278847) ^ 96858905022 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 284473926037278847) ^ 35473001454 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_290833350288569131 : Nat.Prime 290833350288569131 := by
  apply lucas_primality 290833350288569131 (7 : ZMod 290833350288569131)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1384920715659853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1384920715659853, 1)] : List FactorBlock).map factorBlockValue).prod) = 290833350288569131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_1384920715659853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 290833350288569131) ^ 145416675144284565 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 290833350288569131) ^ 96944450096189710 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 290833350288569131) ^ 58166670057713826 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 290833350288569131) ^ 41547621469795590 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 290833350288569131) ^ 210 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_314934424130144519 : Nat.Prime 314934424130144519 := by
  apply lucas_primality 314934424130144519 (7 : ZMod 314934424130144519)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (317, 1), (2689, 1), (7793, 1), (3386393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (317, 1), (2689, 1), (7793, 1), (3386393, 1)] : List FactorBlock).map factorBlockValue).prod) = 314934424130144519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_317
      · exact prime_twentyThreeU_2689
      · exact prime_twentyThreeU_7793
      · exact prime_twentyThreeU_3386393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 314934424130144519) ^ 157467212065072259 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 314934424130144519) ^ 44990632018592074 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 314934424130144519) ^ 993483987792254 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 314934424130144519) ^ 117119532960262 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 314934424130144519) ^ 40412475828326 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 314934424130144519) ^ 92999963126 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_388752391739653339 : Nat.Prime 388752391739653339 := by
  apply lucas_primality 388752391739653339 (2 : ZMod 388752391739653339)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (64792065289942223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (64792065289942223, 1)] : List FactorBlock).map factorBlockValue).prod) = 388752391739653339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_64792065289942223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 388752391739653339) ^ 194376195869826669 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 388752391739653339) ^ 129584130579884446 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 388752391739653339) ^ 6 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_504093009929136949 : Nat.Prime 504093009929136949 := by
  apply lucas_primality 504093009929136949 (2 : ZMod 504093009929136949)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (971, 1), (1602309601687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (971, 1), (1602309601687, 1)] : List FactorBlock).map factorBlockValue).prod) = 504093009929136949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_971
      · exact prime_twentyThreeU_1602309601687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 504093009929136949) ^ 252046504964568474 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 168031003309712316 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 519148310946588 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 504093009929136949) ^ 314604 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_637594244628013609 : Nat.Prime 637594244628013609 := by
  apply lucas_primality 637594244628013609 (7 : ZMod 637594244628013609)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (107556384046561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (107556384046561, 1)] : List FactorBlock).map factorBlockValue).prod) = 637594244628013609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_twentyThreeU_107556384046561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 637594244628013609) ^ 318797122314006804 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 212531414876004536 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 49045711125231816 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 33557591822527032 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 637594244628013609) ^ 5928 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1320638944293473437 : Nat.Prime 1320638944293473437 := by
  apply lucas_primality 1320638944293473437 (2 : ZMod 1320638944293473437)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (787, 1), (15537659940391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (787, 1), (15537659940391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1320638944293473437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_787
      · exact prime_twentyThreeU_15537659940391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1320638944293473437) ^ 660319472146736718 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1320638944293473437) ^ 440212981431157812 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1320638944293473437) ^ 1678067273562228 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1320638944293473437) ^ 84996 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1506411850697512189 : Nat.Prime 1506411850697512189 := by
  apply lucas_primality 1506411850697512189 (2 : ZMod 1506411850697512189)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (562934174401163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (562934174401163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1506411850697512189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_223
      · exact prime_twentyThreeU_562934174401163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1506411850697512189) ^ 753205925348756094 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506411850697512189) ^ 502137283565837396 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506411850697512189) ^ 6755210092813956 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506411850697512189) ^ 2676 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1645665403986616709 : Nat.Prime 1645665403986616709 := by
  apply lucas_primality 1645665403986616709 (2 : ZMod 1645665403986616709)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (439, 1), (4325423, 1), (216664841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (439, 1), (4325423, 1), (216664841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1645665403986616709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_439
      · exact prime_twentyThreeU_4325423
      · exact prime_twentyThreeU_216664841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1645665403986616709) ^ 822832701993308354 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645665403986616709) ^ 3748668346210972 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645665403986616709) ^ 380463460796 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645665403986616709) ^ 7595442788 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2101331033418299021 : Nat.Prime 2101331033418299021 := by
  apply lucas_primality 2101331033418299021 (2 : ZMod 2101331033418299021)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (2011, 1), (4018917173657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (2011, 1), (4018917173657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2101331033418299021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_twentyThreeU_2011
      · exact prime_twentyThreeU_4018917173657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2101331033418299021) ^ 1050665516709149510 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 420266206683659804 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 161640848724484540 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 1044918465150820 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2101331033418299021) ^ 522860 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2220757758308832079 : Nat.Prime 2220757758308832079 := by
  apply lucas_primality 2220757758308832079 (3 : ZMod 2220757758308832079)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (59, 2), (607, 1), (653, 1), (723053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (59, 2), (607, 1), (653, 1), (723053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220757758308832079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_t64_607
      · exact prime_twentyThreeU_653
      · exact prime_twentyThreeU_723053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220757758308832079) ^ 1110378879154416039 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 740252586102944026 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 317251108329833154 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 41901089779411926 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 37639962005234442 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3658579502979954 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3400854147486726 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220757758308832079) ^ 3071362345926 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2389657054025455673 : Nat.Prime 2389657054025455673 := by
  apply lucas_primality 2389657054025455673 (3 : ZMod 2389657054025455673)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (12987266597964433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (12987266597964433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2389657054025455673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_twentyThreeU_12987266597964433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2389657054025455673) ^ 1194828527012727836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389657054025455673) ^ 103898132783715464 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2389657054025455673) ^ 184 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3788700684736981361 : Nat.Prime 3788700684736981361 := by
  apply lucas_primality 3788700684736981361 (3 : ZMod 3788700684736981361)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (14699, 1), (209159, 1), (15404087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (14699, 1), (209159, 1), (15404087, 1)] : List FactorBlock).map factorBlockValue).prod) = 3788700684736981361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_twentyThreeU_14699
      · exact prime_twentyThreeU_209159
      · exact prime_twentyThreeU_15404087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3788700684736981361) ^ 1894350342368490680 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3788700684736981361) ^ 757740136947396272 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3788700684736981361) ^ 257752274626640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3788700684736981361) ^ 18113973985040 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 3788700684736981361) ^ 245954251280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3991405277342233507 : Nat.Prime 3991405277342233507 := by
  apply lucas_primality 3991405277342233507 (2 : ZMod 3991405277342233507)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (95033458984338893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (95033458984338893, 1)] : List FactorBlock).map factorBlockValue).prod) = 3991405277342233507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_twentyThreeU_95033458984338893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3991405277342233507) ^ 1995702638671116753 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991405277342233507) ^ 1330468425780744502 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991405277342233507) ^ 570200753906033358 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3991405277342233507) ^ 42 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_5486517298236998423 : Nat.Prime 5486517298236998423 := by
  apply lucas_primality 5486517298236998423 (5 : ZMod 5486517298236998423)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5807, 1), (1927729, 1), (35008291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5807, 1), (1927729, 1), (35008291, 1)] : List FactorBlock).map factorBlockValue).prod) = 5486517298236998423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_5807
      · exact prime_twentyThreeU_1927729
      · exact prime_twentyThreeU_35008291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5486517298236998423) ^ 2743258649118499211 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5486517298236998423) ^ 783788185462428346 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5486517298236998423) ^ 944810969215946 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5486517298236998423) ^ 2846104041718 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5486517298236998423) ^ 156720512242 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_7308654782304413917 : Nat.Prime 7308654782304413917 := by
  apply lucas_primality 7308654782304413917 (2 : ZMod 7308654782304413917)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (29, 1), (140813, 1), (308793623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (29, 1), (140813, 1), (308793623, 1)] : List FactorBlock).map factorBlockValue).prod) = 7308654782304413917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_twentyThreeU_140813
      · exact prime_twentyThreeU_308793623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7308654782304413917) ^ 3654327391152206958 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 2436218260768137972 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 1044093540329201988 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 317767599230626692 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 252022578700152204 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 51903267328332 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7308654782304413917) ^ 23668412292 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_14858475635311999991 : Nat.Prime 14858475635311999991 := by
  apply lucas_primality 14858475635311999991 (22 : ZMod 14858475635311999991)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (433, 1), (769, 1), (12113, 1), (28337723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (433, 1), (769, 1), (12113, 1), (28337723, 1)] : List FactorBlock).map factorBlockValue).prod) = 14858475635311999991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_433
      · exact prime_twentyThreeU_769
      · exact prime_twentyThreeU_12113
      · exact prime_twentyThreeU_28337723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 14858475635311999991) ^ 7429237817655999995 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 2971695127062399998 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 1142959664254769230 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 34315186224739030 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 19321814870366710 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 1226655298878230 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 14858475635311999991) ^ 524335552130 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_20197150530475483867 : Nat.Prime 20197150530475483867 := by
  apply lucas_primality 20197150530475483867 (2 : ZMod 20197150530475483867)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 4), (19, 1), (277, 1), (283, 1), (941297459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 4), (19, 1), (277, 1), (283, 1), (941297459, 1)] : List FactorBlock).map factorBlockValue).prod) = 20197150530475483867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_twentyThreeU_277
      · exact prime_t64_283
      · exact prime_twentyThreeU_941297459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20197150530475483867) ^ 10098575265237741933 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 6732383510158494622 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 2885307218639354838 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 1063007922656604414 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 72913900832041458 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 71368023075885102 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20197150530475483867) ^ 21456714174 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_40535782307780493691 : Nat.Prime 40535782307780493691 := by
  apply lucas_primality 40535782307780493691 (11 : ZMod 40535782307780493691)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (22397, 1), (1001081, 1), (1826183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (22397, 1), (1001081, 1), (1826183, 1)] : List FactorBlock).map factorBlockValue).prod) = 40535782307780493691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_twentyThreeU_22397
      · exact prime_twentyThreeU_1001081
      · exact prime_twentyThreeU_1826183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 40535782307780493691) ^ 20267891153890246845 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 13511927435926831230 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 8107156461556098738 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 3685071118889135790 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 1809875532784770 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 40492010444490 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (11 : ZMod 40535782307780493691) ^ 22196999045430 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_94740369555121501163 : Nat.Prime 94740369555121501163 := by
  apply lucas_primality 94740369555121501163 (2 : ZMod 94740369555121501163)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (12433, 1), (9225270165289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (12433, 1), (9225270165289, 1)] : List FactorBlock).map factorBlockValue).prod) = 94740369555121501163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_59
      · exact prime_twentyThreeU_12433
      · exact prime_twentyThreeU_9225270165289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94740369555121501163) ^ 47370184777560750581 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 13534338507874500166 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 1605768975510533918 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 7620073156528714 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 94740369555121501163) ^ 10269658 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_96584909776364242577 : Nat.Prime 96584909776364242577 := by
  apply lucas_primality 96584909776364242577 (3 : ZMod 96584909776364242577)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (2801, 1), (535939, 1), (574463957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (2801, 1), (535939, 1), (574463957, 1)] : List FactorBlock).map factorBlockValue).prod) = 96584909776364242577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_2801
      · exact prime_twentyThreeU_535939
      · exact prime_twentyThreeU_574463957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96584909776364242577) ^ 48292454888182121288 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 13797844253766320368 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 34482295528869776 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 180216236878384 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 96584909776364242577) ^ 168130495568 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_131336119686186864173 : Nat.Prime 131336119686186864173 := by
  apply lucas_primality 131336119686186864173 (2 : ZMod 131336119686186864173)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4963961, 1), (6614481846563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4963961, 1), (6614481846563, 1)] : List FactorBlock).map factorBlockValue).prod) = 131336119686186864173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_4963961
      · exact prime_twentyThreeU_6614481846563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131336119686186864173) ^ 65668059843093432086 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131336119686186864173) ^ 26457927386252 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131336119686186864173) ^ 19855844 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_377719370248179368459 : Nat.Prime 377719370248179368459 := by
  apply lucas_primality 377719370248179368459 (2 : ZMod 377719370248179368459)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 2), (19, 1), (107, 1), (90191, 1), (509146541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 2), (19, 1), (107, 1), (90191, 1), (509146541, 1)] : List FactorBlock).map factorBlockValue).prod) = 377719370248179368459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_107
      · exact prime_twentyThreeU_90191
      · exact prime_twentyThreeU_509146541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 377719370248179368459) ^ 188859685124089684229 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 53959910035454195494 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 22218786485187021674 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 19879966855167335182 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 3530087572412891294 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 4187994037633238 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 377719370248179368459) ^ 741867693938 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_635056563217686509789 : Nat.Prime 635056563217686509789 := by
  apply lucas_primality 635056563217686509789 (2 : ZMod 635056563217686509789)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2413558747, 1), (9397157443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2413558747, 1), (9397157443, 1)] : List FactorBlock).map factorBlockValue).prod) = 635056563217686509789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_2413558747
      · exact prime_twentyThreeU_9397157443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 635056563217686509789) ^ 317528281608843254894 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 90722366173955215684 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 263120408404 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 635056563217686509789) ^ 67579644916 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_766767074547667312331 : Nat.Prime 766767074547667312331 := by
  apply lucas_primality 766767074547667312331 (2 : ZMod 766767074547667312331)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (739, 1), (1250088974921609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (739, 1), (1250088974921609, 1)] : List FactorBlock).map factorBlockValue).prod) = 766767074547667312331 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_83
      · exact prime_twentyThreeU_739
      · exact prime_twentyThreeU_1250088974921609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 766767074547667312331) ^ 383383537273833656165 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 153353414909533462466 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 9238157524670690510 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 1037573849184935470 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 766767074547667312331) ^ 613370 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1489823689991846453869 : Nat.Prime 1489823689991846453869 := by
  apply lucas_primality 1489823689991846453869 (2 : ZMod 1489823689991846453869)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (107, 1), (89253755690860679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (107, 1), (89253755690860679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1489823689991846453869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_107
      · exact prime_twentyThreeU_89253755690860679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1489823689991846453869) ^ 744911844995923226934 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1489823689991846453869) ^ 496607896663948817956 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1489823689991846453869) ^ 114601822307065111836 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1489823689991846453869) ^ 13923585887774265924 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1489823689991846453869) ^ 16692 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_1579001519726932154947 : Nat.Prime 1579001519726932154947 := by
  apply lucas_primality 1579001519726932154947 (2 : ZMod 1579001519726932154947)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (311, 1), (116858741, 1), (7241186041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (311, 1), (116858741, 1), (7241186041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579001519726932154947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_311
      · exact prime_twentyThreeU_116858741
      · exact prime_twentyThreeU_7241186041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1579001519726932154947) ^ 789500759863466077473 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579001519726932154947) ^ 526333839908977384982 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579001519726932154947) ^ 5077175304588206286 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579001519726932154947) ^ 13512053152506 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579001519726932154947) ^ 218058410706 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2179506374964796177897 : Nat.Prime 2179506374964796177897 := by
  apply lucas_primality 2179506374964796177897 (10 : ZMod 2179506374964796177897)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1365547, 1), (66502848765757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1365547, 1), (66502848765757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179506374964796177897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_1365547
      · exact prime_twentyThreeU_66502848765757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2179506374964796177897) ^ 1089753187482398088948 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2179506374964796177897) ^ 726502124988265392632 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2179506374964796177897) ^ 1596068370378168 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 2179506374964796177897) ^ 32773128 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2709298883243373764647 : Nat.Prime 2709298883243373764647 := by
  apply lucas_primality 2709298883243373764647 (5 : ZMod 2709298883243373764647)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (563, 1), (3169, 1), (11003914253261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (563, 1), (3169, 1), (11003914253261, 1)] : List FactorBlock).map factorBlockValue).prod) = 2709298883243373764647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_563
      · exact prime_twentyThreeU_3169
      · exact prime_twentyThreeU_11003914253261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2709298883243373764647) ^ 1354649441621686882323 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 903099627747791254882 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 117795603619277120202 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 4812253789064607042 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 854938113992860134 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 2709298883243373764647) ^ 246212286 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3072449687012719116881 : Nat.Prime 3072449687012719116881 := by
  apply lucas_primality 3072449687012719116881 (6 : ZMod 3072449687012719116881)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (5486517298236998423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (5486517298236998423, 1)] : List FactorBlock).map factorBlockValue).prod) = 3072449687012719116881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_twentyThreeU_5486517298236998423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3072449687012719116881) ^ 1536224843506359558440 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3072449687012719116881) ^ 614489937402543823376 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3072449687012719116881) ^ 438921383858959873840 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3072449687012719116881) ^ 560 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_10908844429150004333813 : Nat.Prime 10908844429150004333813 := by
  apply lucas_primality 10908844429150004333813 (2 : ZMod 10908844429150004333813)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (173, 1), (563, 1), (1473705342963913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (173, 1), (563, 1), (1473705342963913, 1)] : List FactorBlock).map factorBlockValue).prod) = 10908844429150004333813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_twentyThreeU_173
      · exact prime_t64_563
      · exact prime_twentyThreeU_1473705342963913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10908844429150004333813) ^ 5454422214575002166906 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10908844429150004333813) ^ 574149706797368649148 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10908844429150004333813) ^ 63056904214739909444 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10908844429150004333813) ^ 19376277849289528124 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 10908844429150004333813) ^ 7402324 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_11131280792565475419677 : Nat.Prime 11131280792565475419677 := by
  apply lucas_primality 11131280792565475419677 (2 : ZMod 11131280792565475419677)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (89, 1), (1645665403986616709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (89, 1), (1645665403986616709, 1)] : List FactorBlock).map factorBlockValue).prod) = 11131280792565475419677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_89
      · exact prime_twentyThreeU_1645665403986616709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11131280792565475419677) ^ 5565640396282737709838 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11131280792565475419677) ^ 585856883819235548404 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11131280792565475419677) ^ 125070570702982869884 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11131280792565475419677) ^ 6764 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_13242326888996687561549 : Nat.Prime 13242326888996687561549 := by
  apply lucas_primality 13242326888996687561549 (3 : ZMod 13242326888996687561549)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (12659, 1), (44651977, 1), (836693087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (12659, 1), (44651977, 1), (836693087, 1)] : List FactorBlock).map factorBlockValue).prod) = 13242326888996687561549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_twentyThreeU_12659
      · exact prime_twentyThreeU_44651977
      · exact prime_twentyThreeU_836693087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13242326888996687561549) ^ 6621163444498343780774 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13242326888996687561549) ^ 1891760984142383937364 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13242326888996687561549) ^ 1046080013349923972 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13242326888996687561549) ^ 296567538073324 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 13242326888996687561549) ^ 15826982551604 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_21502713789964432889971 : Nat.Prime 21502713789964432889971 := by
  apply lucas_primality 21502713789964432889971 (22 : ZMod 21502713789964432889971)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2087, 1), (294347, 1), (1166782634291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2087, 1), (294347, 1), (1166782634291, 1)] : List FactorBlock).map factorBlockValue).prod) = 21502713789964432889971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_2087
      · exact prime_twentyThreeU_294347
      · exact prime_twentyThreeU_1166782634291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 21502713789964432889971) ^ 10751356894982216444985 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 21502713789964432889971) ^ 7167571263321477629990 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 21502713789964432889971) ^ 4300542757992886577994 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 21502713789964432889971) ^ 10303169041669589310 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 21502713789964432889971) ^ 73052260732959510 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (22 : ZMod 21502713789964432889971) ^ 18429065670 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_52818729525591298226101 : Nat.Prime 52818729525591298226101 := by
  apply lucas_primality 52818729525591298226101 (10 : ZMod 52818729525591298226101)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (11, 1), (13, 1), (149, 1), (2754375428293847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (11, 1), (13, 1), (149, 1), (2754375428293847, 1)] : List FactorBlock).map factorBlockValue).prod) = 52818729525591298226101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_149
      · exact prime_twentyThreeU_2754375428293847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 52818729525591298226101) ^ 26409364762795649113050 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 17606243175197099408700 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 10563745905118259645220 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 4801702684144663475100 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 4062979194276253709700 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 354488117621418108900 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (10 : ZMod 52818729525591298226101) ^ 19176300 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_92116162030274707997999 : Nat.Prime 92116162030274707997999 := by
  apply lucas_primality 92116162030274707997999 (13 : ZMod 92116162030274707997999)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2709298883243373764647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2709298883243373764647, 1)] : List FactorBlock).map factorBlockValue).prod) = 92116162030274707997999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_twentyThreeU_2709298883243373764647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 92116162030274707997999) ^ 46058081015137353998999 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 92116162030274707997999) ^ 5418597766486747529294 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (13 : ZMod 92116162030274707997999) ^ 34 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_94873064777838334750193 : Nat.Prime 94873064777838334750193 := by
  apply lucas_primality 94873064777838334750193 (3 : ZMod 94873064777838334750193)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (541, 1), (8781491, 1), (33733056821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (541, 1), (8781491, 1), (33733056821, 1)] : List FactorBlock).map factorBlockValue).prod) = 94873064777838334750193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_twentyThreeU_541
      · exact prime_twentyThreeU_8781491
      · exact prime_twentyThreeU_33733056821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94873064777838334750193) ^ 47436532388919167375096 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94873064777838334750193) ^ 2564136885887522560816 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94873064777838334750193) ^ 175366108646651265712 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94873064777838334750193) ^ 10803753574175312 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 94873064777838334750193) ^ 2812465685552 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_120314937233924959084463 : Nat.Prime 120314937233924959084463 := by
  apply lucas_primality 120314937233924959084463 (5 : ZMod 120314937233924959084463)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1584080819, 1), (1026385466377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1584080819, 1), (1026385466377, 1)] : List FactorBlock).map factorBlockValue).prod) = 120314937233924959084463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_twentyThreeU_1584080819
      · exact prime_twentyThreeU_1026385466377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 120314937233924959084463) ^ 60157468616962479542231 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 3251755060376350245526 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 75952524511898 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 120314937233924959084463) ^ 117221980606 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_161498439986963023701767 : Nat.Prime 161498439986963023701767 := by
  apply lucas_primality 161498439986963023701767 (5 : ZMod 161498439986963023701767)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7039, 1), (12375743, 1), (926949530179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7039, 1), (12375743, 1), (926949530179, 1)] : List FactorBlock).map factorBlockValue).prod) = 161498439986963023701767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_7039
      · exact prime_twentyThreeU_12375743
      · exact prime_twentyThreeU_926949530179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 161498439986963023701767) ^ 80749219993481511850883 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 161498439986963023701767) ^ 22943378318932095994 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 161498439986963023701767) ^ 13049595485859962 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 161498439986963023701767) ^ 174225709954 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_430044413885039176238891 : Nat.Prime 430044413885039176238891 := by
  apply lucas_primality 430044413885039176238891 (7 : ZMod 430044413885039176238891)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (43, 1), (151, 1), (9662041, 1), (97926671179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (43, 1), (151, 1), (9662041, 1), (97926671179, 1)] : List FactorBlock).map factorBlockValue).prod) = 430044413885039176238891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_43
      · exact prime_twentyThreeU_151
      · exact prime_twentyThreeU_9662041
      · exact prime_twentyThreeU_97926671179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 430044413885039176238891) ^ 215022206942519588119445 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 86008882777007835247778 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 61434916269291310891270 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 10001032881047422703230 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 2847976250894299180390 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 44508651317567290 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (7 : ZMod 430044413885039176238891) ^ 4391494254910 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_578666943337339323546239 : Nat.Prime 578666943337339323546239 := by
  apply lucas_primality 578666943337339323546239 (17 : ZMod 578666943337339323546239)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2203, 1), (131336119686186864173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2203, 1), (131336119686186864173, 1)] : List FactorBlock).map factorBlockValue).prod) = 578666943337339323546239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_2203
      · exact prime_twentyThreeU_131336119686186864173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 578666943337339323546239) ^ 289333471668669661773119 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 578666943337339323546239) ^ 262672239372373728346 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (17 : ZMod 578666943337339323546239) ^ 4406 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_796955988697682067783157 : Nat.Prime 796955988697682067783157 := by
  apply lucas_primality 796955988697682067783157 (5 : ZMod 796955988697682067783157)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (701, 1), (94740369555121501163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (701, 1), (94740369555121501163, 1)] : List FactorBlock).map factorBlockValue).prod) = 796955988697682067783157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_701
      · exact prime_twentyThreeU_94740369555121501163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 796955988697682067783157) ^ 398477994348841033891578 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 265651996232560689261052 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 1136884434661458013956 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 796955988697682067783157) ^ 8412 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2751405275155814241906437 : Nat.Prime 2751405275155814241906437 := by
  apply lucas_primality 2751405275155814241906437 (2 : ZMod 2751405275155814241906437)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (73, 1), (3079, 1), (278207824421392157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (73, 1), (3079, 1), (278207824421392157, 1)] : List FactorBlock).map factorBlockValue).prod) = 2751405275155814241906437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_73
      · exact prime_twentyThreeU_3079
      · exact prime_twentyThreeU_278207824421392157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2751405275155814241906437) ^ 1375702637577907120953218 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2751405275155814241906437) ^ 250127752286892203809676 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2751405275155814241906437) ^ 37690483221312523861732 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2751405275155814241906437) ^ 893603532041511608284 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2751405275155814241906437) ^ 9889748 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_8662675480842597054081337 : Nat.Prime 8662675480842597054081337 := by
  apply lucas_primality 8662675480842597054081337 (5 : ZMod 8662675480842597054081337)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (120314937233924959084463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (120314937233924959084463, 1)] : List FactorBlock).map factorBlockValue).prod) = 8662675480842597054081337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_120314937233924959084463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8662675480842597054081337) ^ 4331337740421298527040668 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8662675480842597054081337) ^ 2887558493614199018027112 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8662675480842597054081337) ^ 72 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_8837224028067894752278621 : Nat.Prime 8837224028067894752278621 := by
  apply lucas_primality 8837224028067894752278621 (6 : ZMod 8837224028067894752278621)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (1117, 1), (305351, 1), (756593, 1), (190251689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (1117, 1), (305351, 1), (756593, 1), (190251689, 1)] : List FactorBlock).map factorBlockValue).prod) = 8837224028067894752278621 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_twentyThreeU_1117
      · exact prime_twentyThreeU_305351
      · exact prime_twentyThreeU_756593
      · exact prime_twentyThreeU_190251689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8837224028067894752278621) ^ 4418612014033947376139310 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 2945741342689298250759540 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 1767444805613578950455724 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 7911570302657023054860 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 28941198909019111620 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 11680287853664909340 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 8837224028067894752278621) ^ 46450173843491580 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_11473476090449330022262159 : Nat.Prime 11473476090449330022262159 := by
  apply lucas_primality 11473476090449330022262159 (6 : ZMod 11473476090449330022262159)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (7283, 1), (20197150530475483867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (7283, 1), (20197150530475483867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11473476090449330022262159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_twentyThreeU_7283
      · exact prime_twentyThreeU_20197150530475483867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11473476090449330022262159) ^ 5736738045224665011131079 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 3824492030149776674087386 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 882575083880717694020166 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 1575377741377087741626 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (6 : ZMod 11473476090449330022262159) ^ 568074 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_14502473778327953148139369 : Nat.Prime 14502473778327953148139369 := by
  apply lucas_primality 14502473778327953148139369 (79 : ZMod 14502473778327953148139369)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4877, 1), (103573, 1), (3269711, 1), (365866097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4877, 1), (103573, 1), (3269711, 1), (365866097, 1)] : List FactorBlock).map factorBlockValue).prod) = 14502473778327953148139369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_twentyThreeU_4877
      · exact prime_twentyThreeU_103573
      · exact prime_twentyThreeU_3269711
      · exact prime_twentyThreeU_365866097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 14502473778327953148139369) ^ 7251236889163976574069684 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (79 : ZMod 14502473778327953148139369) ^ 4834157926109317716046456 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (79 : ZMod 14502473778327953148139369) ^ 2973646458545817746184 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (79 : ZMod 14502473778327953148139369) ^ 140021760288182761416 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (79 : ZMod 14502473778327953148139369) ^ 4435399268720676888 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (79 : ZMod 14502473778327953148139369) ^ 39638747337466344 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_382987863864294537362835449 : Nat.Prime 382987863864294537362835449 := by
  apply lucas_primality 382987863864294537362835449 (3 : ZMod 382987863864294537362835449)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (170365511, 1), (281004545474211721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (170365511, 1), (281004545474211721, 1)] : List FactorBlock).map factorBlockValue).prod) = 382987863864294537362835449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_twentyThreeU_170365511
      · exact prime_twentyThreeU_281004545474211721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 382987863864294537362835449) ^ 191493931932147268681417724 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 382987863864294537362835449) ^ 2248036363793693768 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (3 : ZMod 382987863864294537362835449) ^ 1362924088 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_647431865103926479827650401 : Nat.Prime 647431865103926479827650401 := by
  apply lucas_primality 647431865103926479827650401 (127 : ZMod 647431865103926479827650401)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 647431865103926479827650401 - 1 by
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
    · change (127 : ZMod 647431865103926479827650401) ^ 323715932551963239913825200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 215810621701308826609216800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 129486373020785295965530080 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 92490266443418068546807200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 58857442282175134529786400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 49802451161840498448280800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 38084227359054498813391200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 34075361321259288411981600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 28149211526257673035984800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 22325236727721602752677600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 20884898874320209026698400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 17498158516322337292639200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 15791021100095767800674400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 15056555002416894879712800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 13775146066040988932503200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 12215695567998612826936800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 10973421442439431861485600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (127 : ZMod 647431865103926479827650401) ^ 10613637132851253767666400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_755337175954580893132258801 : Nat.Prime 755337175954580893132258801 := by
  apply lucas_primality 755337175954580893132258801 (71 : ZMod 755337175954580893132258801)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 755337175954580893132258801 - 1 by
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
    · change (71 : ZMod 755337175954580893132258801) ^ 377668587977290446566129400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 251779058651526964377419600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 151067435190916178626451760 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 107905310850654413304608400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 68667015995870990284750800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 58102859688813914856327600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 44431598585563581948956400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 39754588208135836480645200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 32840746780633951875315600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 26046109515675203211457200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 24365715353373577197814800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 20414518269042726841412400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 18422857950111729100786800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 17565980836153044026331600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 16071003743714487087920400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 14251644829331714964759600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 12802325016179337171733200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (71 : ZMod 755337175954580893132258801) ^ 12382576654993129395610800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_2719213833436491215276131681 : Nat.Prime 2719213833436491215276131681 := by
  apply lucas_primality 2719213833436491215276131681 (67 : ZMod 2719213833436491215276131681)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719213833436491215276131681 - 1 by
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
    · change (67 : ZMod 2719213833436491215276131681) ^ 1359606916718245607638065840 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 906404611145497071758710560 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 543842766687298243055226336 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 388459119062355887896590240 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 247201257585135565025102880 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 209170294879730093482779360 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 159953754908028895016243040 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 143116517549289011330322720 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 118226688410282226751136160 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 93765994256430731561245920 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 87716575272144877912133280 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 73492265768553816629084640 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 66322288620402224762832480 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 63237531010150958494793760 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 57855613477372153516513440 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 51305921385594173873134560 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 46088370058245613818239520 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (67 : ZMod 2719213833436491215276131681) ^ 44577275957975265824198880 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_3021348703818323572529035201 : Nat.Prime 3021348703818323572529035201 := by
  apply lucas_primality 3021348703818323572529035201 (73 : ZMod 3021348703818323572529035201)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3021348703818323572529035201 - 1 by
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
    · change (73 : ZMod 3021348703818323572529035201) ^ 1510674351909161786264517600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 1007116234606107857509678400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 604269740763664714505807040 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 431621243402617653218433600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 274668063983483961139003200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 232411438755255659425310400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 177726394342254327795825600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 159018352832543345922580800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 131362987122535807501262400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 104184438062700812845828800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 97462861413494308791259200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 81658073076170907365649600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 73691431800446916403147200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 70263923344612176105326400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 64284014974857948351681600 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 57006579317326859859038400 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 51209300064717348686932800 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (73 : ZMod 3021348703818323572529035201) ^ 49530306619972517582443200 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem prime_twentyThreeU_27192138334364912152761316867 : Nat.Prime 27192138334364912152761316867 := by
  apply lucas_primality 27192138334364912152761316867 (2 : ZMod 27192138334364912152761316867)
  · rw [← twentyThreeUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37013, 1), (11131280792565475419677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37013, 1), (11131280792565475419677, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_twentyThreeU_37013
      · exact prime_twentyThreeU_11131280792565475419677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27192138334364912152761316867) ^ 13596069167182456076380658433 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364912152761316867) ^ 9064046111454970717587105622 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364912152761316867) ^ 2472012575851355650251028806 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364912152761316867) ^ 734664532309321377698682 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364912152761316867) ^ 2442858 ≠ 1
      rw [← twentyThreeUFastPow_eq_pow]
      decide

private theorem phi_twentyThreeU_27192138334364912152761316800 : Nat.totient 27192138334364912152761316800 = 3578141474565294705868800000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 2), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316800 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316801 : Nat.totient 27192138334364912152761316801 = 27123638399188497816369342480 := by
  rw [← show ((([(397, 1), (4609763, 1), (14858475635311999991, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_397, prime_twentyThreeU_4609763, prime_twentyThreeU_14858475635311999991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316802 : Nat.totient 27192138334364912152761316802 = 13366186282538825515165900800 := by
  rw [← show ((([(2, 1), (107, 1), (131, 1), (133660878913, 1), (7256947469281, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_107, prime_twentyThreeU_131, prime_twentyThreeU_133660878913, prime_twentyThreeU_7256947469281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316803 : Nat.totient 27192138334364912152761316803 = 17825904664842595427241696000 := by
  rw [← show ((([(3, 1), (67, 1), (571, 1), (52051, 1), (7369849, 1), (617623095907, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_67, prime_twentyThreeU_571, prime_twentyThreeU_52051, prime_twentyThreeU_7369849, prime_twentyThreeU_617623095907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316804 : Nat.totient 27192138334364912152761316804 = 13596069162403141962640198784 := by
  rw [← show ((([(2, 2), (2844774137, 1), (2389657054025455673, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyThreeU_2844774137, prime_twentyThreeU_2389657054025455673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316805 : Nat.totient 27192138334364912152761316805 = 21671414279039831300776800000 := by
  rw [← show ((([(5, 1), (277, 1), (6451, 1), (53819, 1), (46324247, 1), (1220738251, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_twentyThreeU_277, prime_twentyThreeU_6451, prime_twentyThreeU_53819, prime_twentyThreeU_46324247, prime_twentyThreeU_1220738251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316806 : Nat.totient 27192138334364912152761316806 = 9063861879130910168171011208 := by
  rw [← show ((([(2, 1), (3, 1), (49199, 1), (92116162030274707997999, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_49199, prime_twentyThreeU_92116162030274707997999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316807 : Nat.totient 27192138334364912152761316807 = 23242615705469605199457212928 := by
  rw [← show ((([(7, 1), (359, 1), (2970797, 1), (279560689, 1), (13028721283, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_twentyThreeU_359, prime_twentyThreeU_2970797, prime_twentyThreeU_279560689, prime_twentyThreeU_13028721283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316808 : Nat.totient 27192138334364912152761316808 = 13404575156569036027217616000 := by
  rw [← show ((([(2, 3), (71, 1), (170365511, 1), (281004545474211721, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_71, prime_twentyThreeU_170365511, prime_twentyThreeU_281004545474211721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316809 : Nat.totient 27192138334364912152761316809 = 18128092222909941435174211200 := by
  rw [← show ((([(3, 2), (3021348703818323572529035201, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyThreeU_3021348703818323572529035201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316810 : Nat.totient 27192138334364912152761316810 = 10876855333745964861104526720 := by
  rw [← show ((([(2, 1), (5, 1), (2719213833436491215276131681, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyThreeU_2719213833436491215276131681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316811 : Nat.totient 27192138334364912152761316811 = 24704685305701779257285952000 := by
  rw [← show ((([(11, 1), (1601, 1), (1009161947, 1), (1530024826764883, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_twentyThreeU_1601, prime_twentyThreeU_1009161947, prime_twentyThreeU_1530024826764883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316812 : Nat.totient 27192138334364912152761316812 = 8975740713745530626911360000 := by
  rw [← show ((([(2, 2), (3, 1), (173, 1), (251, 1), (989777, 1), (52723584966097631, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_173, prime_t64_251, prime_twentyThreeU_989777, prime_twentyThreeU_52723584966097631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316813 : Nat.totient 27192138334364912152761316813 = 25100251211812731893060131584 := by
  rw [← show ((([(13, 1), (136303, 1), (1140538079, 1), (13455034150673, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_twentyThreeU_136303, prime_twentyThreeU_1140538079, prime_twentyThreeU_13455034150673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316814 : Nat.totient 27192138334364912152761316814 = 11600878623239306697558312960 := by
  rw [← show ((([(2, 1), (7, 1), (337, 1), (677, 1), (13613, 1), (38803, 1), (16116755127691, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyThreeU_337, prime_twentyThreeU_677, prime_twentyThreeU_13613, prime_twentyThreeU_38803, prime_twentyThreeU_16116755127691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316815 : Nat.totient 27192138334364912152761316815 = 14502473005648674937075275776 := by
  rw [← show ((([(3, 1), (5, 1), (18769073, 1), (96584909776364242577, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyThreeU_18769073, prime_twentyThreeU_96584909776364242577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316816 : Nat.totient 27192138334364912152761316816 = 13594126927979163298664287104 := by
  rw [← show ((([(2, 4), (7517, 1), (101807, 1), (2220757758308832079, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyThreeU_7517, prime_twentyThreeU_101807, prime_twentyThreeU_2220757758308832079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316817 : Nat.totient 27192138334364912152761316817 = 25451205200835536886562425600 := by
  rw [← show ((([(17, 1), (181, 1), (8837224028067894752278621, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_twentyThreeU_181, prime_twentyThreeU_8837224028067894752278621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316818 : Nat.totient 27192138334364912152761316818 = 9064046111454309015007614072 := by
  rw [← show ((([(2, 1), (3, 2), (16027271091163, 1), (94256492157427, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_16027271091163, prime_twentyThreeU_94256492157427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316819 : Nat.totient 27192138334364912152761316819 = 25494695107795660378105184256 := by
  rw [← show ((([(19, 1), (97, 1), (56437, 1), (104009, 1), (6260129, 1), (401513269, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_t64_97, prime_twentyThreeU_56437, prime_twentyThreeU_104009, prime_twentyThreeU_6260129, prime_twentyThreeU_401513269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316820 : Nat.totient 27192138334364912152761316820 = 10876432783909760130718512000 := by
  rw [← show ((([(2, 2), (5, 1), (25741, 1), (52818729525591298226101, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyThreeU_25741, prime_twentyThreeU_52818729525591298226101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316821 : Nat.totient 27192138334364912152761316821 = 15533204229527615045748706800 := by
  rw [← show ((([(3, 1), (7, 1), (3011, 1), (430044413885039176238891, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentyThreeU_3011, prime_twentyThreeU_430044413885039176238891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316822 : Nat.totient 27192138334364912152761316822 = 12360055211586032774565901000 := by
  rw [← show ((([(2, 1), (11, 1), (1611971, 1), (766767074547667312331, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyThreeU_1611971, prime_twentyThreeU_766767074547667312331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316823 : Nat.totient 27192138334364912152761316823 = 25752206212772504069021476224 := by
  rw [← show ((([(23, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316824 : Nat.totient 27192138334364912152761316824 = 9057841573620223665121591296 := by
  rw [← show ((([(2, 3), (3, 1), (1499, 1), (63667, 1), (1216489, 1), (1318897, 1), (7399409, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_1499, prime_twentyThreeU_63667, prime_twentyThreeU_1216489, prime_twentyThreeU_1318897, prime_twentyThreeU_7399409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316825 : Nat.totient 27192138334364912152761316825 = 21736806173780630858462472000 := by
  rw [← show ((([(5, 2), (1291, 1), (400943, 1), (2101331033418299021, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_twentyThreeU_1291, prime_twentyThreeU_400943, prime_twentyThreeU_2101331033418299021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316826 : Nat.totient 27192138334364912152761316826 = 12550107505629522004003301760 := by
  rw [← show ((([(2, 1), (13, 1), (113903, 1), (3330424087, 1), (2756990764841, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_twentyThreeU_113903, prime_twentyThreeU_3330424087, prime_twentyThreeU_2756990764841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316827 : Nat.totient 27192138334364912152761316827 = 18128007783865758228817651200 := by
  rw [← show ((([(3, 4), (214691, 1), (27262846097, 1), (57355267721, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_twentyThreeU_214691, prime_twentyThreeU_27262846097, prime_twentyThreeU_57355267721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316828 : Nat.totient 27192138334364912152761316828 = 11538381615778656441496512000 := by
  rw [← show ((([(2, 2), (7, 1), (101, 1), (1469231, 1), (56041753, 1), (116778303307, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_101, prime_twentyThreeU_1469231, prime_twentyThreeU_56041753, prime_twentyThreeU_116778303307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316829 : Nat.totient 27192138334364912152761316829 = 26254453968680248522637569920 := by
  rw [← show ((([(29, 1), (1076003, 1), (1137479177, 1), (766105227571, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_twentyThreeU_1076003, prime_twentyThreeU_1137479177, prime_twentyThreeU_766105227571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316830 : Nat.totient 27192138334364912152761316830 = 7159449080440381933891586592 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (79, 1), (11473476090449330022262159, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_79, prime_twentyThreeU_11473476090449330022262159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316831 : Nat.totient 27192138334364912152761316831 = 26306508306212477235408852000 := by
  rw [← show ((([(31, 1), (3109, 1), (177900851, 1), (1585926001599839, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_twentyThreeU_3109, prime_twentyThreeU_177900851, prime_twentyThreeU_1585926001599839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316832 : Nat.totient 27192138334364912152761316832 = 13595566950369947571163645440 := by
  rw [← show ((([(2, 5), (27077, 1), (149921671, 1), (209328529952453, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyThreeU_27077, prime_twentyThreeU_149921671, prime_twentyThreeU_209328529952453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316833 : Nat.totient 27192138334364912152761316833 = 16479929498054791734734772960 := by
  rw [← show ((([(3, 1), (11, 2), (116927, 1), (1230067, 1), (520826605545199, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentyThreeU_116927, prime_twentyThreeU_1230067, prime_twentyThreeU_520826605545199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316834 : Nat.totient 27192138334364912152761316834 = 12795806279532323530637168640 := by
  rw [← show ((([(2, 1), (17, 1), (39679, 1), (74561, 1), (270328603841520479, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyThreeU_39679, prime_twentyThreeU_74561, prime_twentyThreeU_270328603841520479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316835 : Nat.totient 27192138334364912152761316835 = 18646037714977573807770078336 := by
  rw [← show ((([(5, 1), (7, 1), (1204531986989, 1), (644995937440229, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_twentyThreeU_1204531986989, prime_twentyThreeU_644995937440229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316836 : Nat.totient 27192138334364912152761316836 = 9064046111454970717587105600 := by
  rw [← show ((([(2, 2), (3, 2), (755337175954580893132258801, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_755337175954580893132258801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316837 : Nat.totient 27192138334364912152761316837 = 26455023444407000035772066688 := by
  rw [← show ((([(37, 1), (13177, 1), (143467, 1), (388752391739653339, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_twentyThreeU_13177, prime_twentyThreeU_143467, prime_twentyThreeU_388752391739653339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316838 : Nat.totient 27192138334364912152761316838 = 12879013003803551702675520000 := by
  rw [← show ((([(2, 1), (19, 1), (8741, 1), (2960967601, 1), (27648080720861, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentyThreeU_8741, prime_twentyThreeU_2960967601, prime_twentyThreeU_27648080720861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316839 : Nat.totient 27192138334364912152761316839 = 16733608349020890254119764096 := by
  rw [← show ((([(3, 1), (13, 1), (1097909, 1), (635056563217686509789, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_twentyThreeU_1097909, prime_twentyThreeU_635056563217686509789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316840 : Nat.totient 27192138334364912152761316840 = 10864104037926801948019982592 := by
  rw [← show ((([(2, 3), (5, 1), (853, 1), (796955988697682067783157, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyThreeU_853, prime_twentyThreeU_796955988697682067783157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316841 : Nat.totient 27192138334364912152761316841 = 26295268562571937084682803200 := by
  rw [← show ((([(41, 1), (139, 1), (661, 1), (9349, 1), (198223, 1), (3895148684197, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_139, prime_t64_661, prime_twentyThreeU_9349, prime_twentyThreeU_198223, prime_twentyThreeU_3895148684197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316842 : Nat.totient 27192138334364912152761316842 = 7769182381247117757931804800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (647431865103926479827650401, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentyThreeU_647431865103926479827650401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316843 : Nat.totient 27192138334364912152761316843 = 26195930654068013491541960064 := by
  rw [← show ((([(43, 1), (73, 1), (8662675480842597054081337, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_73, prime_twentyThreeU_8662675480842597054081337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316844 : Nat.totient 27192138334364912152761316844 = 12324646509735988932163813440 := by
  rw [← show ((([(2, 2), (11, 1), (349, 1), (17199463, 1), (102955693875907123, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_349, prime_twentyThreeU_17199463, prime_twentyThreeU_102955693875907123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316845 : Nat.totient 27192138334364912152761316845 = 14502264292373188410838245888 := by
  rw [← show ((([(3, 2), (5, 1), (69233, 1), (1157796803, 1), (7538507136859, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyThreeU_69233, prime_twentyThreeU_1157796803, prime_twentyThreeU_7538507136859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316846 : Nat.totient 27192138334364912152761316846 = 13004935714494069398408534200 := by
  rw [← show ((([(2, 1), (23, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316847 : Nat.totient 27192138334364912152761316847 = 26576265401163536020157310336 := by
  rw [← show ((([(47, 2), (733, 1), (26339, 1), (637594244628013609, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_twentyThreeU_733, prime_twentyThreeU_26339, prime_twentyThreeU_637594244628013609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316848 : Nat.totient 27192138334364912152761316848 = 9062948966756244827742178560 := by
  rw [← show ((([(2, 4), (3, 1), (8263, 1), (45098231, 1), (1520214477104117, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_8263, prime_twentyThreeU_45098231, prime_twentyThreeU_1520214477104117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316849 : Nat.totient 27192138334364912152761316849 = 23137419062400175512672780192 := by
  rw [← show ((([(7, 3), (137, 1), (578666943337339323546239, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_137, prime_twentyThreeU_578666943337339323546239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316850 : Nat.totient 27192138334364912152761316850 = 10876112048602824327097620480 := by
  rw [← show ((([(2, 1), (5, 2), (20129, 1), (53597, 1), (504093009929136949, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_twentyThreeU_20129, prime_twentyThreeU_53597, prime_twentyThreeU_504093009929136949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316851 : Nat.totient 27192138334364912152761316851 = 17061664112652416594913736704 := by
  rw [← show ((([(3, 1), (17, 1), (244633, 1), (2179506374964796177897, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_twentyThreeU_244633, prime_twentyThreeU_2179506374964796177897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316852 : Nat.totient 27192138334364912152761316852 = 12540541119166482668572999680 := by
  rw [← show ((([(2, 2), (13, 1), (1297, 1), (54527953, 1), (7394023845594961, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_twentyThreeU_1297, prime_twentyThreeU_54527953, prime_twentyThreeU_7394023845594961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316853 : Nat.totient 27192138334364912152761316853 = 26544999798986736780417646656 := by
  rw [← show ((([(53, 1), (199, 1), (1952227, 1), (1320638944293473437, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_twentyThreeU_199, prime_twentyThreeU_1952227, prime_twentyThreeU_1320638944293473437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316854 : Nat.totient 27192138334364912152761316854 = 9061623165381480955555545600 := by
  rw [← show ((([(2, 1), (3, 3), (3761, 1), (722581, 1), (22958359, 1), (8070842779, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_3761, prime_twentyThreeU_722581, prime_twentyThreeU_22958359, prime_twentyThreeU_8070842779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316855 : Nat.totient 27192138334364912152761316855 = 19776100037619666066124656000 := by
  rw [← show ((([(5, 1), (11, 1), (35570789, 1), (1872272351, 1), (7423661299, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_twentyThreeU_35570789, prime_twentyThreeU_1872272351, prime_twentyThreeU_7423661299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316856 : Nat.totient 27192138334364912152761316856 = 11653505361673703194514284800 := by
  rw [← show ((([(2, 3), (7, 1), (43801, 1), (5424319, 1), (2043742075411279, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_twentyThreeU_43801, prime_twentyThreeU_5424319, prime_twentyThreeU_2043742075411279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316857 : Nat.totient 27192138334364912152761316857 = 17084947049893650675667288320 := by
  rw [← show ((([(3, 1), (19, 1), (197, 1), (9199, 1), (920562037, 1), (285962179991, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_t64_197, prime_twentyThreeU_9199, prime_twentyThreeU_920562037, prime_twentyThreeU_285962179991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316858 : Nat.totient 27192138334364912152761316858 = 13122717239580667453910698096 := by
  rw [← show ((([(2, 1), (29, 1), (2903, 1), (161498439986963023701767, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_twentyThreeU_2903, prime_twentyThreeU_161498439986963023701767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316859 : Nat.totient 27192138334364912152761316859 = 26540489144178166433194346400 := by
  rw [← show ((([(59, 1), (151, 1), (1933, 1), (1579001519726932154947, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_twentyThreeU_151, prime_twentyThreeU_1933, prime_twentyThreeU_1579001519726932154947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316860 : Nat.totient 27192138334364912152761316860 = 7250878827868275454531522560 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (20333, 1), (5044997, 1), (4418040956711281, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentyThreeU_20333, prime_twentyThreeU_5044997, prime_twentyThreeU_4418040956711281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316861 : Nat.totient 27192138334364912152761316861 = 26745075411957761628544686000 := by
  rw [← show ((([(61, 1), (20731, 1), (21502713789964432889971, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_twentyThreeU_20731, prime_twentyThreeU_21502713789964432889971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316862 : Nat.totient 27192138334364912152761316862 = 13157486290819732089666821760 := by
  rw [← show ((([(2, 1), (31, 1), (7402100472937, 1), (59251137966073, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_twentyThreeU_7402100472937, prime_twentyThreeU_59251137966073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316863 : Nat.totient 27192138334364912152761316863 = 15538364751156596197839993744 := by
  rw [← show ((([(3, 2), (7, 1), (1370511479, 1), (314934424130144519, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_twentyThreeU_1370511479, prime_twentyThreeU_314934424130144519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316864 : Nat.totient 27192138334364912152761316864 = 13556653791390709640554217472 := by
  rw [← show ((([(2, 9), (643, 1), (743, 1), (64400449, 1), (1726174584847, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_twentyThreeU_643, prime_twentyThreeU_743, prime_twentyThreeU_64400449, prime_twentyThreeU_1726174584847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316865 : Nat.totient 27192138334364912152761316865 = 20080347057229344780907063296 := by
  rw [← show ((([(5, 1), (13, 1), (17042393, 1), (276055733, 1), (88920655909, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_twentyThreeU_17042393, prime_twentyThreeU_276055733, prime_twentyThreeU_88920655909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316866 : Nat.totient 27192138334364912152761316866 = 8239819293888667524660962240 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (37013, 1), (11131280792565475419677, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_twentyThreeU_37013, prime_twentyThreeU_11131280792565475419677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316867 : Nat.totient 27192138334364912152761316867 = 27192138334364912152761316866 := by
  rw [← show ((([(27192138334364912152761316867, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_27192138334364912152761316867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316868 : Nat.totient 27192138334364912152761316868 = 12795177840046895929803116544 := by
  rw [← show ((([(2, 2), (17, 1), (12613, 1), (118453, 1), (267651688908085609, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_twentyThreeU_12613, prime_twentyThreeU_118453, prime_twentyThreeU_267651688908085609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316869 : Nat.totient 27192138334364912152761316869 = 17339914300174726590166636800 := by
  rw [← show ((([(3, 1), (23, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316870 : Nat.totient 27192138334364912152761316870 = 9041049520122647127329551872 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (67, 1), (83, 1), (383, 1), (1103, 1), (32707, 1), (5055654984467, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_67, prime_t64_83, prime_t64_383, prime_t64_1103, prime_twentyThreeU_32707, prime_twentyThreeU_5055654984467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316871 : Nat.totient 27192138334364912152761316871 = 27189386929089756338519400552 := by
  rw [← show ((([(9883, 1), (2751405275155814241906437, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_9883, prime_twentyThreeU_2751405275155814241906437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316872 : Nat.totient 27192138334364912152761316872 = 9063972372662482412325350400 := by
  rw [← show ((([(2, 3), (3, 2), (122921, 1), (3072449687012719116881, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_122921, prime_twentyThreeU_3072449687012719116881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316873 : Nat.totient 27192138334364912152761316873 = 27176195731058309403840223488 := by
  rw [← show ((([(2129, 1), (8573, 1), (1489823689991846453869, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_2129, prime_twentyThreeU_8573, prime_twentyThreeU_1489823689991846453869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316874 : Nat.totient 27192138334364912152761316874 = 13228131114571683112482020544 := by
  rw [← show ((([(2, 1), (37, 1), (27749, 1), (13242326888996687561549, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_twentyThreeU_27749, prime_twentyThreeU_13242326888996687561549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316875 : Nat.totient 27192138334364912152761316875 = 14502473778327953148139368000 := by
  rw [← show ((([(3, 1), (5, 4), (14502473778327953148139369, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_twentyThreeU_14502473778327953148139369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316876 : Nat.totient 27192138334364912152761316876 = 12880379648237643317303668800 := by
  rw [← show ((([(2, 2), (19, 1), (122957, 1), (5921543, 1), (491407321771651, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_twentyThreeU_122957, prime_twentyThreeU_5921543, prime_twentyThreeU_491407321771651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316877 : Nat.totient 27192138334364912152761316877 = 20993858316598029039006036480 := by
  rw [← show ((([(7, 1), (11, 1), (109, 1), (49459, 1), (4307423, 1), (15207691149977, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_109, prime_twentyThreeU_49459, prime_twentyThreeU_4307423, prime_twentyThreeU_15207691149977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316878 : Nat.totient 27192138334364912152761316878 = 8366811795188247470696153088 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (12973925065313, 1), (26870600560577, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_twentyThreeU_12973925065313, prime_twentyThreeU_26870600560577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316879 : Nat.totient 27192138334364912152761316879 = 26809150470500617615398481360 := by
  rw [← show ((([(71, 1), (382987863864294537362835449, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_71, prime_twentyThreeU_382987863864294537362835449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316880 : Nat.totient 27192138334364912152761316880 = 10753579818316807056950830080 := by
  rw [← show ((([(2, 4), (5, 1), (89, 1), (10111, 1), (377719370248179368459, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_89, prime_twentyThreeU_10111, prime_twentyThreeU_377719370248179368459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316881 : Nat.totient 27192138334364912152761316881 = 18025087535535718558674544896 := by
  rw [← show ((([(3, 3), (229, 1), (757, 1), (4289167079, 1), (1354488340669, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_229, prime_twentyThreeU_757, prime_twentyThreeU_4289167079, prime_twentyThreeU_1354488340669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316882 : Nat.totient 27192138334364912152761316882 = 13221826418508901637070528000 := by
  rw [← show ((([(2, 1), (41, 1), (331, 1), (5171, 1), (11570412613, 1), (16744729277, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_twentyThreeU_331, prime_twentyThreeU_5171, prime_twentyThreeU_11570412613, prime_twentyThreeU_16744729277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316883 : Nat.totient 27192138334364912152761316883 = 27192138334323194702560026960 := by
  rw [← show ((([(651827067131, 1), (41716798374222793, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_651827067131, prime_twentyThreeU_41716798374222793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316884 : Nat.totient 27192138334364912152761316884 = 7768622760791874770860651008 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (13883, 1), (3800098483, 1), (6136007748209, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_twentyThreeU_13883, prime_twentyThreeU_3800098483, prime_twentyThreeU_6136007748209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316885 : Nat.totient 27192138334364912152761316885 = 20474080609614364073212704000 := by
  rw [← show ((([(5, 1), (17, 1), (1099968451, 1), (290833350288569131, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_twentyThreeU_1099968451, prime_twentyThreeU_290833350288569131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316886 : Nat.totient 27192138334364912152761316886 = 13279879809628844356798345800 := by
  rw [← show ((([(2, 1), (43, 1), (7800211, 1), (40535782307780493691, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_twentyThreeU_7800211, prime_twentyThreeU_40535782307780493691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316887 : Nat.totient 27192138334364912152761316887 = 17502921102470834776996320000 := by
  rw [← show ((([(3, 1), (29, 1), (271451, 1), (1379682971, 1), (834551915881, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_twentyThreeU_271451, prime_twentyThreeU_1379682971, prime_twentyThreeU_834551915881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316888 : Nat.totient 27192138334364912152761316888 = 12356267956665664717865006080 := by
  rw [← show ((([(2, 3), (11, 1), (3257, 1), (94873064777838334750193, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_twentyThreeU_3257, prime_twentyThreeU_94873064777838334750193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316889 : Nat.totient 27192138334364912152761316889 = 27192138332858500284012872400 := by
  rw [← show ((([(18050932301, 1), (1506411850697512189, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_18050932301, prime_twentyThreeU_1506411850697512189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316890 : Nat.totient 27192138334364912152761316890 = 7251236889161323053341752800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (2803786716131, 1), (107759576947691, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_twentyThreeU_2803786716131, prime_twentyThreeU_107759576947691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316891 : Nat.totient 27192138334364912152761316891 = 21514658635647500483134671840 := by
  rw [← show ((([(7, 1), (13, 2), (80800891, 1), (284473926037278847, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_twentyThreeU_80800891, prime_twentyThreeU_284473926037278847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316892 : Nat.totient 27192138334364912152761316892 = 13004935103799090642577102848 := by
  rw [← show ((([(2, 2), (23, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316893 : Nat.totient 27192138334364912152761316893 = 17492679297099506906138707200 := by
  rw [← show ((([(3, 1), (31, 1), (347, 1), (222403, 1), (3788700684736981361, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_twentyThreeU_347, prime_twentyThreeU_222403, prime_twentyThreeU_3788700684736981361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316894 : Nat.totient 27192138334364912152761316894 = 13276672043383686912957091200 := by
  rw [← show ((([(2, 1), (47, 1), (443, 1), (163601, 1), (3991405277342233507, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_twentyThreeU_443, prime_twentyThreeU_163601, prime_twentyThreeU_3991405277342233507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316895 : Nat.totient 27192138334364912152761316895 = 20608778000874473302828892544 := by
  rw [← show ((([(5, 1), (19, 1), (39163573, 1), (7308654782304413917, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316895 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_twentyThreeU_39163573, prime_twentyThreeU_7308654782304413917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316896 : Nat.totient 27192138334364912152761316896 = 9064046111453647677900012800 := by
  rw [← show ((([(2, 5), (3, 1), (8668303629341, 1), (32676686592311, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316896 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_twentyThreeU_8668303629341, prime_twentyThreeU_32676686592311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316897 : Nat.totient 27192138334364912152761316897 = 27150586545934279786251334320 := by
  rw [← show ((([(839, 1), (2971, 1), (10908844429150004333813, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316897 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_twentyThreeU_839, prime_twentyThreeU_2971, prime_twentyThreeU_10908844429150004333813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316898 : Nat.totient 27192138334364912152761316898 = 11634549377891573861690941440 := by
  rw [← show ((([(2, 1), (7, 2), (641, 1), (11177, 1), (4562707, 1), (8488118303299, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316898 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_641, prime_twentyThreeU_11177, prime_twentyThreeU_4562707, prime_twentyThreeU_8488118303299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_twentyThreeU_27192138334364912152761316899 : Nat.totient 27192138334364912152761316899 = 16480083839006991785528455920 := by
  rw [← show ((([(3, 2), (11, 1), (13048881437167, 1), (21049165425103, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364912152761316899 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_twentyThreeU_13048881437167, prime_twentyThreeU_21049165425103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64TwentyThreeU : certifiedKill 1 27192138334364912152761316799 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_twentyThreeU_27192138334364912152761316800, phi_twentyThreeU_27192138334364912152761316801, phi_twentyThreeU_27192138334364912152761316802,
    phi_twentyThreeU_27192138334364912152761316803, phi_twentyThreeU_27192138334364912152761316804, phi_twentyThreeU_27192138334364912152761316805,
    phi_twentyThreeU_27192138334364912152761316806, phi_twentyThreeU_27192138334364912152761316807, phi_twentyThreeU_27192138334364912152761316808,
    phi_twentyThreeU_27192138334364912152761316809, phi_twentyThreeU_27192138334364912152761316810, phi_twentyThreeU_27192138334364912152761316811,
    phi_twentyThreeU_27192138334364912152761316812, phi_twentyThreeU_27192138334364912152761316813, phi_twentyThreeU_27192138334364912152761316814,
    phi_twentyThreeU_27192138334364912152761316815, phi_twentyThreeU_27192138334364912152761316816, phi_twentyThreeU_27192138334364912152761316817,
    phi_twentyThreeU_27192138334364912152761316818, phi_twentyThreeU_27192138334364912152761316819, phi_twentyThreeU_27192138334364912152761316820,
    phi_twentyThreeU_27192138334364912152761316821, phi_twentyThreeU_27192138334364912152761316822, phi_twentyThreeU_27192138334364912152761316823,
    phi_twentyThreeU_27192138334364912152761316824, phi_twentyThreeU_27192138334364912152761316825, phi_twentyThreeU_27192138334364912152761316826,
    phi_twentyThreeU_27192138334364912152761316827, phi_twentyThreeU_27192138334364912152761316828, phi_twentyThreeU_27192138334364912152761316829,
    phi_twentyThreeU_27192138334364912152761316830, phi_twentyThreeU_27192138334364912152761316831, phi_twentyThreeU_27192138334364912152761316832,
    phi_twentyThreeU_27192138334364912152761316833, phi_twentyThreeU_27192138334364912152761316834, phi_twentyThreeU_27192138334364912152761316835,
    phi_twentyThreeU_27192138334364912152761316836, phi_twentyThreeU_27192138334364912152761316837, phi_twentyThreeU_27192138334364912152761316838,
    phi_twentyThreeU_27192138334364912152761316839, phi_twentyThreeU_27192138334364912152761316840, phi_twentyThreeU_27192138334364912152761316841,
    phi_twentyThreeU_27192138334364912152761316842, phi_twentyThreeU_27192138334364912152761316843, phi_twentyThreeU_27192138334364912152761316844,
    phi_twentyThreeU_27192138334364912152761316845, phi_twentyThreeU_27192138334364912152761316846, phi_twentyThreeU_27192138334364912152761316847,
    phi_twentyThreeU_27192138334364912152761316848, phi_twentyThreeU_27192138334364912152761316849, phi_twentyThreeU_27192138334364912152761316850,
    phi_twentyThreeU_27192138334364912152761316851, phi_twentyThreeU_27192138334364912152761316852, phi_twentyThreeU_27192138334364912152761316853,
    phi_twentyThreeU_27192138334364912152761316854, phi_twentyThreeU_27192138334364912152761316855, phi_twentyThreeU_27192138334364912152761316856,
    phi_twentyThreeU_27192138334364912152761316857, phi_twentyThreeU_27192138334364912152761316858, phi_twentyThreeU_27192138334364912152761316859,
    phi_twentyThreeU_27192138334364912152761316860, phi_twentyThreeU_27192138334364912152761316861, phi_twentyThreeU_27192138334364912152761316862,
    phi_twentyThreeU_27192138334364912152761316863, phi_twentyThreeU_27192138334364912152761316864, phi_twentyThreeU_27192138334364912152761316865,
    phi_twentyThreeU_27192138334364912152761316866, phi_twentyThreeU_27192138334364912152761316867, phi_twentyThreeU_27192138334364912152761316868,
    phi_twentyThreeU_27192138334364912152761316869, phi_twentyThreeU_27192138334364912152761316870, phi_twentyThreeU_27192138334364912152761316871,
    phi_twentyThreeU_27192138334364912152761316872, phi_twentyThreeU_27192138334364912152761316873, phi_twentyThreeU_27192138334364912152761316874,
    phi_twentyThreeU_27192138334364912152761316875, phi_twentyThreeU_27192138334364912152761316876, phi_twentyThreeU_27192138334364912152761316877,
    phi_twentyThreeU_27192138334364912152761316878, phi_twentyThreeU_27192138334364912152761316879, phi_twentyThreeU_27192138334364912152761316880,
    phi_twentyThreeU_27192138334364912152761316881, phi_twentyThreeU_27192138334364912152761316882, phi_twentyThreeU_27192138334364912152761316883,
    phi_twentyThreeU_27192138334364912152761316884, phi_twentyThreeU_27192138334364912152761316885, phi_twentyThreeU_27192138334364912152761316886,
    phi_twentyThreeU_27192138334364912152761316887, phi_twentyThreeU_27192138334364912152761316888, phi_twentyThreeU_27192138334364912152761316889,
    phi_twentyThreeU_27192138334364912152761316890, phi_twentyThreeU_27192138334364912152761316891, phi_twentyThreeU_27192138334364912152761316892,
    phi_twentyThreeU_27192138334364912152761316893, phi_twentyThreeU_27192138334364912152761316894, phi_twentyThreeU_27192138334364912152761316895,
    phi_twentyThreeU_27192138334364912152761316896, phi_twentyThreeU_27192138334364912152761316897, phi_twentyThreeU_27192138334364912152761316898,
    phi_twentyThreeU_27192138334364912152761316899]

end TotientTailPeriodKiller
end Erdos249257
