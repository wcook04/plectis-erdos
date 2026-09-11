import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000
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
  prime_t64_191
  prime_t64_197
  prime_t64_227
  prime_t64_229
  prime_t64_233
  prime_t64_239
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_283
  prime_t64_307
  prime_t64_311
  prime_t64_349
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_461
  prime_t64_491
  prime_t64_563
  prime_t64_661
  prime_t64_991
  prime_t64_1051
  prime_t64_1061
  prime_t64_1213
  prime_t64_1483
  prime_t64_1669
  prime_t64_2281
  prime_t64_2417
  prime_t64_2897
  prime_t64_2963
  prime_t64_4327
  prime_t64_4787
  prime_t64_5009
  prime_t64_6151
  prime_t64_10337
  prime_t64_38329
  prime_t64_45127
  prime_t64_97523
  prime_t64_210193
  prime_t64_623279
  prime_t64_1214459
  prime_t64_2072201
  prime_t64_2567179
  prime_t64_9492089
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private theorem prime_free64OctF_127 : Nat.Prime 127 := by norm_num
private theorem prime_free64OctF_131 : Nat.Prime 131 := by norm_num
private theorem prime_free64OctF_173 : Nat.Prime 173 := by norm_num
private theorem prime_free64OctF_181 : Nat.Prime 181 := by norm_num
private theorem prime_free64OctF_199 : Nat.Prime 199 := by norm_num
private theorem prime_free64OctF_211 : Nat.Prime 211 := by norm_num
private theorem prime_free64OctF_241 : Nat.Prime 241 := by norm_num
private theorem prime_free64OctF_271 : Nat.Prime 271 := by norm_num
private theorem prime_free64OctF_277 : Nat.Prime 277 := by norm_num
private theorem prime_free64OctF_293 : Nat.Prime 293 := by norm_num
private theorem prime_free64OctF_313 : Nat.Prime 313 := by norm_num
private theorem prime_free64OctF_347 : Nat.Prime 347 := by norm_num
private theorem prime_free64OctF_359 : Nat.Prime 359 := by norm_num
private theorem prime_free64OctF_367 : Nat.Prime 367 := by norm_num
private theorem prime_free64OctF_373 : Nat.Prime 373 := by norm_num
private theorem prime_free64OctF_379 : Nat.Prime 379 := by norm_num
private theorem prime_free64OctF_389 : Nat.Prime 389 := by norm_num
private theorem prime_free64OctF_397 : Nat.Prime 397 := by norm_num
private theorem prime_free64OctF_401 : Nat.Prime 401 := by norm_num
private theorem prime_free64OctF_419 : Nat.Prime 419 := by norm_num
private theorem prime_free64OctF_463 : Nat.Prime 463 := by norm_num
private theorem prime_free64OctF_503 : Nat.Prime 503 := by norm_num
private theorem prime_free64OctF_509 : Nat.Prime 509 := by norm_num
private theorem prime_free64OctF_541 : Nat.Prime 541 := by norm_num
private theorem prime_free64OctF_547 : Nat.Prime 547 := by norm_num
private theorem prime_free64OctF_557 : Nat.Prime 557 := by norm_num
private theorem prime_free64OctF_569 : Nat.Prime 569 := by norm_num
private theorem prime_free64OctF_577 : Nat.Prime 577 := by norm_num
private theorem prime_free64OctF_631 : Nat.Prime 631 := by norm_num
private theorem prime_free64OctF_677 : Nat.Prime 677 := by norm_num
private theorem prime_free64OctF_709 : Nat.Prime 709 := by norm_num
private theorem prime_free64OctF_727 : Nat.Prime 727 := by norm_num
private theorem prime_free64OctF_739 : Nat.Prime 739 := by norm_num
private theorem prime_free64OctF_743 : Nat.Prime 743 := by norm_num
private theorem prime_free64OctF_757 : Nat.Prime 757 := by norm_num
private theorem prime_free64OctF_827 : Nat.Prime 827 := by norm_num
private theorem prime_free64OctF_853 : Nat.Prime 853 := by norm_num
private theorem prime_free64OctF_863 : Nat.Prime 863 := by norm_num
private theorem prime_free64OctF_877 : Nat.Prime 877 := by norm_num
private theorem prime_free64OctF_887 : Nat.Prime 887 := by norm_num
private theorem prime_free64OctF_953 : Nat.Prime 953 := by norm_num
private theorem prime_free64OctF_971 : Nat.Prime 971 := by norm_num
private theorem prime_free64OctF_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_free64OctF_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_free64OctF_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_free64OctF_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_free64OctF_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_free64OctF_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_free64OctF_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_free64OctF_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_free64OctF_1427 : Nat.Prime 1427 := by norm_num
private theorem prime_free64OctF_1489 : Nat.Prime 1489 := by norm_num
private theorem prime_free64OctF_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_free64OctF_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_free64OctF_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_free64OctF_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_free64OctF_1709 : Nat.Prime 1709 := by norm_num
private theorem prime_free64OctF_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_free64OctF_1787 : Nat.Prime 1787 := by norm_num
private theorem prime_free64OctF_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_free64OctF_1901 : Nat.Prime 1901 := by norm_num
private theorem prime_free64OctF_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_free64OctF_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_free64OctF_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_free64OctF_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_free64OctF_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_free64OctF_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_free64OctF_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_free64OctF_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_free64OctF_2837 : Nat.Prime 2837 := by norm_num
private theorem prime_free64OctF_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_free64OctF_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_free64OctF_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_free64OctF_3259 : Nat.Prime 3259 := by norm_num
private theorem prime_free64OctF_3593 : Nat.Prime 3593 := by norm_num
private theorem prime_free64OctF_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_free64OctF_3823 : Nat.Prime 3823 := by norm_num
private theorem prime_free64OctF_3923 : Nat.Prime 3923 := by norm_num
private theorem prime_free64OctF_4111 : Nat.Prime 4111 := by norm_num
private theorem prime_free64OctF_4201 : Nat.Prime 4201 := by norm_num
private theorem prime_free64OctF_4243 : Nat.Prime 4243 := by norm_num
private theorem prime_free64OctF_5003 : Nat.Prime 5003 := by norm_num
private theorem prime_free64OctF_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_free64OctF_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_free64OctF_5569 : Nat.Prime 5569 := by norm_num
private theorem prime_free64OctF_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_free64OctF_5827 : Nat.Prime 5827 := by norm_num
private theorem prime_free64OctF_5987 : Nat.Prime 5987 := by norm_num
private theorem prime_free64OctF_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_free64OctF_6997 : Nat.Prime 6997 := by norm_num
private theorem prime_free64OctF_7477 : Nat.Prime 7477 := by norm_num
private theorem prime_free64OctF_7549 : Nat.Prime 7549 := by norm_num
private theorem prime_free64OctF_8101 : Nat.Prime 8101 := by norm_num
private theorem prime_free64OctF_8761 : Nat.Prime 8761 := by norm_num
private theorem prime_free64OctF_8837 : Nat.Prime 8837 := by norm_num
private theorem prime_free64OctF_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_free64OctF_8963 : Nat.Prime 8963 := by norm_num
private theorem prime_free64OctF_9043 : Nat.Prime 9043 := by norm_num
private theorem prime_free64OctF_9739 : Nat.Prime 9739 := by norm_num
private theorem prime_free64OctF_10333 : Nat.Prime 10333 := by norm_num
private theorem prime_free64OctF_10739 : Nat.Prime 10739 := by norm_num
private theorem prime_free64OctF_11069 : Nat.Prime 11069 := by norm_num
private theorem prime_free64OctF_11923 : Nat.Prime 11923 := by norm_num
private theorem prime_free64OctF_12097 : Nat.Prime 12097 := by norm_num
private theorem prime_free64OctF_12251 : Nat.Prime 12251 := by norm_num
private theorem prime_free64OctF_13291 : Nat.Prime 13291 := by norm_num
private theorem prime_free64OctF_13789 : Nat.Prime 13789 := by norm_num
private theorem prime_free64OctF_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_free64OctF_15619 : Nat.Prime 15619 := by norm_num
private theorem prime_free64OctF_15667 : Nat.Prime 15667 := by norm_num
private theorem prime_free64OctF_16561 : Nat.Prime 16561 := by norm_num
private theorem prime_free64OctF_16823 : Nat.Prime 16823 := by norm_num
private theorem prime_free64OctF_17417 : Nat.Prime 17417 := by norm_num
private theorem prime_free64OctF_17737 : Nat.Prime 17737 := by norm_num
private theorem prime_free64OctF_18089 : Nat.Prime 18089 := by norm_num
private theorem prime_free64OctF_18713 : Nat.Prime 18713 := by norm_num
private theorem prime_free64OctF_18979 : Nat.Prime 18979 := by norm_num
private theorem prime_free64OctF_19427 : Nat.Prime 19427 := by norm_num
private theorem prime_free64OctF_19763 : Nat.Prime 19763 := by norm_num
private theorem prime_free64OctF_20129 : Nat.Prime 20129 := by norm_num
private theorem prime_free64OctF_20807 : Nat.Prime 20807 := by norm_num
private theorem prime_free64OctF_22397 : Nat.Prime 22397 := by norm_num
private theorem prime_free64OctF_23017 : Nat.Prime 23017 := by norm_num
private theorem prime_free64OctF_25307 : Nat.Prime 25307 := by norm_num
private theorem prime_free64OctF_25373 : Nat.Prime 25373 := by norm_num
private theorem prime_free64OctF_28183 : Nat.Prime 28183 := by norm_num
private theorem prime_free64OctF_28807 : Nat.Prime 28807 := by norm_num
private theorem prime_free64OctF_29021 : Nat.Prime 29021 := by norm_num
private theorem prime_free64OctF_29717 : Nat.Prime 29717 := by norm_num
private theorem prime_free64OctF_30161 : Nat.Prime 30161 := by norm_num
private theorem prime_free64OctF_31723 : Nat.Prime 31723 := by norm_num
private theorem prime_free64OctF_32719 : Nat.Prime 32719 := by norm_num
private theorem prime_free64OctF_32783 : Nat.Prime 32783 := by norm_num
private theorem prime_free64OctF_34273 : Nat.Prime 34273 := by norm_num
private theorem prime_free64OctF_35461 : Nat.Prime 35461 := by norm_num
private theorem prime_free64OctF_41669 : Nat.Prime 41669 := by norm_num
private theorem prime_free64OctF_49627 : Nat.Prime 49627 := by norm_num
private theorem prime_free64OctF_50821 : Nat.Prime 50821 := by norm_num
private theorem prime_free64OctF_50833 : Nat.Prime 50833 := by norm_num
private theorem prime_free64OctF_53269 : Nat.Prime 53269 := by norm_num
private theorem prime_free64OctF_54287 : Nat.Prime 54287 := by norm_num
private theorem prime_free64OctF_54917 : Nat.Prime 54917 := by norm_num
private theorem prime_free64OctF_55843 : Nat.Prime 55843 := by norm_num
private theorem prime_free64OctF_56809 : Nat.Prime 56809 := by norm_num
private theorem prime_free64OctF_58337 : Nat.Prime 58337 := by norm_num
private theorem prime_free64OctF_60427 : Nat.Prime 60427 := by norm_num
private theorem prime_free64OctF_61379 : Nat.Prime 61379 := by norm_num
private theorem prime_free64OctF_64439 : Nat.Prime 64439 := by norm_num
private theorem prime_free64OctF_66569 : Nat.Prime 66569 := by norm_num
private theorem prime_free64OctF_73651 : Nat.Prime 73651 := by norm_num
private theorem prime_free64OctF_73771 : Nat.Prime 73771 := by norm_num
private theorem prime_free64OctF_78649 : Nat.Prime 78649 := by norm_num
private theorem prime_free64OctF_83047 : Nat.Prime 83047 := by norm_num
private theorem prime_free64OctF_85243 : Nat.Prime 85243 := by norm_num
private theorem prime_free64OctF_85313 : Nat.Prime 85313 := by norm_num
private theorem prime_free64OctF_95233 : Nat.Prime 95233 := by norm_num
private theorem prime_free64OctF_102593 : Nat.Prime 102593 := by norm_num
private theorem prime_free64OctF_103393 : Nat.Prime 103393 := by norm_num
private theorem prime_free64OctF_105319 : Nat.Prime 105319 := by norm_num
private theorem prime_free64OctF_105683 : Nat.Prime 105683 := by norm_num
private theorem prime_free64OctF_106363 : Nat.Prime 106363 := by norm_num
private theorem prime_free64OctF_108461 : Nat.Prime 108461 := by norm_num
private theorem prime_free64OctF_109469 : Nat.Prime 109469 := by norm_num
private theorem prime_free64OctF_118373 : Nat.Prime 118373 := by norm_num
private theorem prime_free64OctF_120049 : Nat.Prime 120049 := by norm_num
private theorem prime_free64OctF_140629 : Nat.Prime 140629 := by norm_num
private theorem prime_free64OctF_152287 : Nat.Prime 152287 := by norm_num
private theorem prime_free64OctF_155413 : Nat.Prime 155413 := by norm_num
private theorem prime_free64OctF_158077 : Nat.Prime 158077 := by norm_num
private theorem prime_free64OctF_160663 : Nat.Prime 160663 := by norm_num
private theorem prime_free64OctF_163987 : Nat.Prime 163987 := by norm_num
private theorem prime_free64OctF_169607 : Nat.Prime 169607 := by norm_num
private theorem prime_free64OctF_177409 : Nat.Prime 177409 := by norm_num
private theorem prime_free64OctF_181219 : Nat.Prime 181219 := by norm_num
private theorem prime_free64OctF_193451 : Nat.Prime 193451 := by norm_num
private theorem prime_free64OctF_212573 : Nat.Prime 212573 := by norm_num
private theorem prime_free64OctF_221461 : Nat.Prime 221461 := by norm_num
private theorem prime_free64OctF_222107 : Nat.Prime 222107 := by norm_num
private theorem prime_free64OctF_228581 : Nat.Prime 228581 := by norm_num
private theorem prime_free64OctF_231169 : Nat.Prime 231169 := by norm_num
private theorem prime_free64OctF_239389 : Nat.Prime 239389 := by norm_num
private theorem prime_free64OctF_241567 : Nat.Prime 241567 := by norm_num
private theorem prime_free64OctF_263957 : Nat.Prime 263957 := by norm_num
private theorem prime_free64OctF_265543 : Nat.Prime 265543 := by norm_num
private theorem prime_free64OctF_283163 : Nat.Prime 283163 := by norm_num
private theorem prime_free64OctF_293081 : Nat.Prime 293081 := by norm_num
private theorem prime_free64OctF_300239 : Nat.Prime 300239 := by norm_num
private theorem prime_free64OctF_307381 : Nat.Prime 307381 := by norm_num
private theorem prime_free64OctF_310627 : Nat.Prime 310627 := by norm_num
private theorem prime_free64OctF_330823 : Nat.Prime 330823 := by norm_num
private theorem prime_free64OctF_344213 : Nat.Prime 344213 := by norm_num
private theorem prime_free64OctF_382747 : Nat.Prime 382747 := by norm_num
private theorem prime_free64OctF_384973 : Nat.Prime 384973 := by norm_num
private theorem prime_free64OctF_439577 : Nat.Prime 439577 := by norm_num
private theorem prime_free64OctF_443941 : Nat.Prime 443941 := by norm_num
private theorem prime_free64OctF_472559 : Nat.Prime 472559 := by norm_num
private theorem prime_free64OctF_492979 : Nat.Prime 492979 := by norm_num
private theorem prime_free64OctF_566437 : Nat.Prime 566437 := by norm_num
private theorem prime_free64OctF_595201 : Nat.Prime 595201 := by norm_num
private theorem prime_free64OctF_633799 : Nat.Prime 633799 := by norm_num
private theorem prime_free64OctF_644549 : Nat.Prime 644549 := by norm_num
private theorem prime_free64OctF_656023 : Nat.Prime 656023 := by norm_num
private theorem prime_free64OctF_671903 : Nat.Prime 671903 := by norm_num
private theorem prime_free64OctF_674701 : Nat.Prime 674701 := by norm_num
private theorem prime_free64OctF_685369 : Nat.Prime 685369 := by norm_num
private theorem prime_free64OctF_723721 : Nat.Prime 723721 := by norm_num
private theorem prime_free64OctF_763481 : Nat.Prime 763481 := by norm_num
private theorem prime_free64OctF_775189 : Nat.Prime 775189 := by norm_num
private theorem prime_free64OctF_810941 : Nat.Prime 810941 := by norm_num
private theorem prime_free64OctF_824099 : Nat.Prime 824099 := by norm_num
private theorem prime_free64OctF_834859 : Nat.Prime 834859 := by norm_num
private theorem prime_free64OctF_865483 : Nat.Prime 865483 := by norm_num
private theorem prime_free64OctF_1001401 : Nat.Prime 1001401 := by norm_num
private theorem prime_free64OctF_1107569 : Nat.Prime 1107569 := by norm_num
private theorem prime_free64OctF_1181153 : Nat.Prime 1181153 := by norm_num
private theorem prime_free64OctF_1197263 : Nat.Prime 1197263 := by norm_num
private theorem prime_free64OctF_1256533 : Nat.Prime 1256533 := by norm_num
private theorem prime_free64OctF_1379089 : Nat.Prime 1379089 := by norm_num
private theorem prime_free64OctF_1411603 : Nat.Prime 1411603 := by norm_num
private theorem prime_free64OctF_1427389 : Nat.Prime 1427389 := by norm_num
private theorem prime_free64OctF_1446019 : Nat.Prime 1446019 := by norm_num
private theorem prime_free64OctF_1701179 : Nat.Prime 1701179 := by norm_num
private theorem prime_free64OctF_1973467 : Nat.Prime 1973467 := by norm_num
private theorem prime_free64OctF_2022619 : Nat.Prime 2022619 := by norm_num
private theorem prime_free64OctF_2126213 : Nat.Prime 2126213 := by norm_num
private theorem prime_free64OctF_2182057 : Nat.Prime 2182057 := by norm_num
private theorem prime_free64OctF_2351599 : Nat.Prime 2351599 := by norm_num
private theorem prime_free64OctF_2416913 : Nat.Prime 2416913 := by norm_num
private theorem prime_free64OctF_2675633 : Nat.Prime 2675633 := by norm_num
private theorem prime_free64OctF_2685877 : Nat.Prime 2685877 := by norm_num
private theorem prime_free64OctF_2732549 : Nat.Prime 2732549 := by norm_num
private theorem prime_free64OctF_3322747 : Nat.Prime 3322747 := by norm_num
private theorem prime_free64OctF_3477841 : Nat.Prime 3477841 := by norm_num
private theorem prime_free64OctF_3696923 : Nat.Prime 3696923 := by norm_num
private theorem prime_free64OctF_3709939 : Nat.Prime 3709939 := by norm_num
private theorem prime_free64OctF_3974227 : Nat.Prime 3974227 := by norm_num
private theorem prime_free64OctF_4017173 : Nat.Prime 4017173 := by norm_num
private theorem prime_free64OctF_4203707 : Nat.Prime 4203707 := by norm_num
private theorem prime_free64OctF_4315799 : Nat.Prime 4315799 := by norm_num
private theorem prime_free64OctF_4384091 : Nat.Prime 4384091 := by norm_num
private theorem prime_free64OctF_4597709 : Nat.Prime 4597709 := by norm_num
private theorem prime_free64OctF_4924417 : Nat.Prime 4924417 := by norm_num
private theorem prime_free64OctF_5054317 : Nat.Prime 5054317 := by norm_num
private theorem prime_free64OctF_5315977 : Nat.Prime 5315977 := by norm_num
private theorem prime_free64OctF_5397907 : Nat.Prime 5397907 := by norm_num
private theorem prime_free64OctF_5530901 : Nat.Prime 5530901 := by norm_num
private theorem prime_free64OctF_5646073 : Nat.Prime 5646073 := by norm_num
private theorem prime_free64OctF_5654479 : Nat.Prime 5654479 := by norm_num
private theorem prime_free64OctF_6514591 : Nat.Prime 6514591 := by norm_num
private theorem prime_free64OctF_6643181 : Nat.Prime 6643181 := by norm_num
private theorem prime_free64OctF_7041049 : Nat.Prime 7041049 := by norm_num
private theorem prime_free64OctF_7220867 : Nat.Prime 7220867 := by norm_num
private theorem prime_free64OctF_7487737 : Nat.Prime 7487737 := by norm_num
private theorem prime_free64OctF_7955917 : Nat.Prime 7955917 := by norm_num
private theorem prime_free64OctF_7982567 : Nat.Prime 7982567 := by norm_num
private theorem prime_free64OctF_9160643 : Nat.Prime 9160643 := by norm_num
private theorem prime_free64OctF_9625963 : Nat.Prime 9625963 := by norm_num

private theorem prime_free64OctF_11239603 : Nat.Prime 11239603 := by
  have hfermat : (3 : ZMod 11239603) ^ (11239603 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11239603) ^ ((11239603 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11239603) ^ ((11239603 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11239603) ^ ((11239603 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11239603) ^ ((11239603 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 11239603) ^ ((11239603 - 1) / 8963) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11239603 (3 : ZMod 11239603)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (19, 1), (8963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (19, 1), (8963, 1)] : List FactorBlock).map factorBlockValue).prod = 11239603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_free64OctF_8963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_14839757 : Nat.Prime 14839757 := by
  have hfermat : (2 : ZMod 14839757) ^ (14839757 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 14839757) ^ ((14839757 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 14839757) ^ ((14839757 - 1) / 3709939) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14839757 (2 : ZMod 14839757)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3709939, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3709939, 1)] : List FactorBlock).map factorBlockValue).prod = 14839757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_3709939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_15535361 : Nat.Prime 15535361 := by
  have hfermat : (6 : ZMod 15535361) ^ (15535361 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 15535361) ^ ((15535361 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 15535361) ^ ((15535361 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 15535361) ^ ((15535361 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 15535361) ^ ((15535361 - 1) / 229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15535361 (6 : ZMod 15535361)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (5, 1), (53, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (5, 1), (53, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod = 15535361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_t64_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_18321287 : Nat.Prime 18321287 := by
  have hfermat : (5 : ZMod 18321287) ^ (18321287 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 18321287) ^ ((18321287 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 18321287) ^ ((18321287 - 1) / 9160643) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18321287 (5 : ZMod 18321287)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (9160643, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (9160643, 1)] : List FactorBlock).map factorBlockValue).prod = 18321287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_9160643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_18480383 : Nat.Prime 18480383 := by
  have hfermat : (5 : ZMod 18480383) ^ (18480383 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 18480383) ^ ((18480383 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 18480383) ^ ((18480383 - 1) / 2417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 18480383) ^ ((18480383 - 1) / 3823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18480383 (5 : ZMod 18480383)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2417, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2417, 1), (3823, 1)] : List FactorBlock).map factorBlockValue).prod = 18480383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_2417
      · exact prime_free64OctF_3823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_21263909 : Nat.Prime 21263909 := by
  have hfermat : (2 : ZMod 21263909) ^ (21263909 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 21263909) ^ ((21263909 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 21263909) ^ ((21263909 - 1) / 5315977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21263909 (2 : ZMod 21263909)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5315977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5315977, 1)] : List FactorBlock).map factorBlockValue).prod = 21263909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_5315977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_22595981 : Nat.Prime 22595981 := by
  have hfermat : (3 : ZMod 22595981) ^ (22595981 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 22595981) ^ ((22595981 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 22595981) ^ ((22595981 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 22595981) ^ ((22595981 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 22595981) ^ ((22595981 - 1) / 271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 22595981) ^ ((22595981 - 1) / 379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 22595981 (3 : ZMod 22595981)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (11, 1), (271, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (11, 1), (271, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod = 22595981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64OctF_271
      · exact prime_free64OctF_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_23255671 : Nat.Prime 23255671 := by
  have hfermat : (6 : ZMod 23255671) ^ (23255671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 23255671) ^ ((23255671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 23255671) ^ ((23255671 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 23255671) ^ ((23255671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 23255671) ^ ((23255671 - 1) / 775189) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 23255671 (6 : ZMod 23255671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (775189, 1)] : List FactorBlock).map factorBlockValue).prod = 23255671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_775189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_25817069 : Nat.Prime 25817069 := by
  have hfermat : (2 : ZMod 25817069) ^ (25817069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 25817069) ^ ((25817069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 25817069) ^ ((25817069 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 25817069) ^ ((25817069 - 1) / 50821) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25817069 (2 : ZMod 25817069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (127, 1), (50821, 1)] : List FactorBlock).map factorBlockValue).prod = 25817069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_127
      · exact prime_free64OctF_50821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_51634139 : Nat.Prime 51634139 := by
  have hfermat : (2 : ZMod 51634139) ^ (51634139 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 51634139) ^ ((51634139 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 51634139) ^ ((51634139 - 1) / 25817069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 51634139 (2 : ZMod 51634139)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (25817069, 1)] : List FactorBlock).map factorBlockValue).prod = 51634139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_25817069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_100888969 : Nat.Prime 100888969 := by
  have hfermat : (7 : ZMod 100888969) ^ (100888969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 100888969) ^ ((100888969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 100888969) ^ ((100888969 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 100888969) ^ ((100888969 - 1) / 4203707) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 100888969 (7 : ZMod 100888969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (4203707, 1)] : List FactorBlock).map factorBlockValue).prod = 100888969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_4203707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_116384069 : Nat.Prime 116384069 := by
  have hfermat : (2 : ZMod 116384069) ^ (116384069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 116384069) ^ ((116384069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 116384069) ^ ((116384069 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 116384069) ^ ((116384069 - 1) / 222107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 116384069 (2 : ZMod 116384069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (131, 1), (222107, 1)] : List FactorBlock).map factorBlockValue).prod = 116384069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_131
      · exact prime_free64OctF_222107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_116408777 : Nat.Prime 116408777 := by
  have hfermat : (3 : ZMod 116408777) ^ (116408777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 116408777) ^ ((116408777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 116408777) ^ ((116408777 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 116408777) ^ ((116408777 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 116408777) ^ ((116408777 - 1) / 2269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 116408777 (3 : ZMod 116408777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 2), (53, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 2), (53, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod = 116408777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_53
      · exact prime_free64OctF_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_144417341 : Nat.Prime 144417341 := by
  have hfermat : (2 : ZMod 144417341) ^ (144417341 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 144417341) ^ ((144417341 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 144417341) ^ ((144417341 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 144417341) ^ ((144417341 - 1) / 7220867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 144417341 (2 : ZMod 144417341)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (7220867, 1)] : List FactorBlock).map factorBlockValue).prod = 144417341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_7220867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_219959393 : Nat.Prime 219959393 := by
  have hfermat : (3 : ZMod 219959393) ^ (219959393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 219959393) ^ ((219959393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 219959393) ^ ((219959393 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 219959393) ^ ((219959393 - 1) / 102593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 219959393 (3 : ZMod 219959393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (67, 1), (102593, 1)] : List FactorBlock).map factorBlockValue).prod = 219959393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_67
      · exact prime_free64OctF_102593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_361266151 : Nat.Prime 361266151 := by
  have hfermat : (14 : ZMod 361266151) ^ (361266151 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (14 : ZMod 361266151) ^ ((361266151 - 1) / 547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 361266151 (14 : ZMod 361266151)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (37, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (7, 1), (17, 1), (37, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod = 361266151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_17
      · exact prime_t64_37
      · exact prime_free64OctF_547
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

private theorem prime_free64OctF_186227381 : Nat.Prime 186227381 := by
  have hfermat : (2 : ZMod 186227381) ^ (186227381 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 186227381) ^ ((186227381 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 186227381) ^ ((186227381 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 186227381) ^ ((186227381 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 186227381) ^ ((186227381 - 1) / 229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 186227381) ^ ((186227381 - 1) / 557) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 186227381 (2 : ZMod 186227381)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (73, 1), (229, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (73, 1), (229, 1), (557, 1)] : List FactorBlock).map factorBlockValue).prod = 186227381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_73
      · exact prime_t64_229
      · exact prime_free64OctF_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_372454763 : Nat.Prime 372454763 := by
  have hfermat : (2 : ZMod 372454763) ^ (372454763 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 372454763) ^ ((372454763 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 372454763) ^ ((372454763 - 1) / 186227381) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 372454763 (2 : ZMod 372454763)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (186227381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (186227381, 1)] : List FactorBlock).map factorBlockValue).prod = 372454763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_186227381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_816013327 : Nat.Prime 816013327 := by
  have hfermat : (3 : ZMod 816013327) ^ (816013327 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 816013327) ^ ((816013327 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 816013327) ^ ((816013327 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 816013327) ^ ((816013327 - 1) / 563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 816013327) ^ ((816013327 - 1) / 241567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 816013327 (3 : ZMod 816013327)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (563, 1), (241567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (563, 1), (241567, 1)] : List FactorBlock).map factorBlockValue).prod = 816013327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_563
      · exact prime_free64OctF_241567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1053289273 : Nat.Prime 1053289273 := by
  have hfermat : (5 : ZMod 1053289273) ^ (1053289273 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1053289273) ^ ((1053289273 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1053289273) ^ ((1053289273 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1053289273) ^ ((1053289273 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 1053289273) ^ ((1053289273 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 1053289273) ^ ((1053289273 - 1) / 491) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1053289273 (5 : ZMod 1053289273)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (113, 2), (491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (113, 2), (491, 1)] : List FactorBlock).map factorBlockValue).prod = 1053289273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_113
      · exact prime_t64_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1160118241 : Nat.Prime 1160118241 := by
  have hfermat : (22 : ZMod 1160118241) ^ (1160118241 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (22 : ZMod 1160118241) ^ ((1160118241 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (22 : ZMod 1160118241) ^ ((1160118241 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (22 : ZMod 1160118241) ^ ((1160118241 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (22 : ZMod 1160118241) ^ ((1160118241 - 1) / 2416913) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1160118241 (22 : ZMod 1160118241)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (5, 1), (2416913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (5, 1), (2416913, 1)] : List FactorBlock).map factorBlockValue).prod = 1160118241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_2416913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1559145541 : Nat.Prime 1559145541 := by
  have hfermat : (6 : ZMod 1559145541) ^ (1559145541 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1559145541) ^ ((1559145541 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1559145541) ^ ((1559145541 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1559145541) ^ ((1559145541 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1559145541) ^ ((1559145541 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1559145541) ^ ((1559145541 - 1) / 633799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1559145541 (6 : ZMod 1559145541)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (41, 1), (633799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (41, 1), (633799, 1)] : List FactorBlock).map factorBlockValue).prod = 1559145541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_free64OctF_633799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_42001217 : Nat.Prime 42001217 := by
  have hfermat : (3 : ZMod 42001217) ^ (42001217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 42001217) ^ ((42001217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 42001217) ^ ((42001217 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 42001217) ^ ((42001217 - 1) / 17737) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 42001217 (3 : ZMod 42001217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (37, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod = 42001217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_free64OctF_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1596046247 : Nat.Prime 1596046247 := by
  have hfermat : (5 : ZMod 1596046247) ^ (1596046247 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1596046247) ^ ((1596046247 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1596046247) ^ ((1596046247 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1596046247) ^ ((1596046247 - 1) / 42001217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1596046247 (5 : ZMod 1596046247)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (42001217, 1)] : List FactorBlock).map factorBlockValue).prod = 1596046247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64OctF_42001217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_82455949 : Nat.Prime 82455949 := by
  have hfermat : (2 : ZMod 82455949) ^ (82455949 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 82455949) ^ ((82455949 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 82455949) ^ ((82455949 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 82455949) ^ ((82455949 - 1) / 763481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 82455949 (2 : ZMod 82455949)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (763481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (763481, 1)] : List FactorBlock).map factorBlockValue).prod = 82455949 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_763481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1814030879 : Nat.Prime 1814030879 := by
  have hfermat : (13 : ZMod 1814030879) ^ (1814030879 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 1814030879) ^ ((1814030879 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 1814030879) ^ ((1814030879 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 1814030879) ^ ((1814030879 - 1) / 82455949) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1814030879 (13 : ZMod 1814030879)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (82455949, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (82455949, 1)] : List FactorBlock).map factorBlockValue).prod = 1814030879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64OctF_82455949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_275223371 : Nat.Prime 275223371 := by
  have hfermat : (2 : ZMod 275223371) ^ (275223371 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 275223371) ^ ((275223371 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 275223371) ^ ((275223371 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 275223371) ^ ((275223371 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 275223371) ^ ((275223371 - 1) / 95233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 275223371 (2 : ZMod 275223371)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 2), (95233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 2), (95233, 1)] : List FactorBlock).map factorBlockValue).prod = 275223371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_free64OctF_95233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_2201786969 : Nat.Prime 2201786969 := by
  have hfermat : (3 : ZMod 2201786969) ^ (2201786969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2201786969) ^ ((2201786969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2201786969) ^ ((2201786969 - 1) / 275223371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2201786969 (3 : ZMod 2201786969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (275223371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (275223371, 1)] : List FactorBlock).map factorBlockValue).prod = 2201786969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_275223371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_133260553 : Nat.Prime 133260553 := by
  have hfermat : (7 : ZMod 133260553) ^ (133260553 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 133260553) ^ ((133260553 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 133260553) ^ ((133260553 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 133260553) ^ ((133260553 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 133260553) ^ ((133260553 - 1) / 12097) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 133260553 (7 : ZMod 133260553)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 4), (17, 1), (12097, 1)] : List FactorBlock).map factorBlockValue).prod = 133260553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_free64OctF_12097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_3198253273 : Nat.Prime 3198253273 := by
  have hfermat : (7 : ZMod 3198253273) ^ (3198253273 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 3198253273) ^ ((3198253273 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 3198253273) ^ ((3198253273 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 3198253273) ^ ((3198253273 - 1) / 133260553) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3198253273 (7 : ZMod 3198253273)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (133260553, 1)] : List FactorBlock).map factorBlockValue).prod = 3198253273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_133260553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_4652375513 : Nat.Prime 4652375513 := by
  have hfermat : (3 : ZMod 4652375513) ^ (4652375513 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4652375513) ^ ((4652375513 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4652375513) ^ ((4652375513 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4652375513) ^ ((4652375513 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4652375513) ^ ((4652375513 - 1) / 20129) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4652375513 (3 : ZMod 4652375513)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (167, 1), (173, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (167, 1), (173, 1), (20129, 1)] : List FactorBlock).map factorBlockValue).prod = 4652375513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_167
      · exact prime_free64OctF_173
      · exact prime_free64OctF_20129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_4950090913 : Nat.Prime 4950090913 := by
  have hfermat : (7 : ZMod 4950090913) ^ (4950090913 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 4950090913) ^ ((4950090913 - 1) / 5563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4950090913 (7 : ZMod 4950090913)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (13, 1), (23, 1), (31, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (13, 1), (23, 1), (31, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod = 4950090913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_23
      · exact prime_t64_31
      · exact prime_free64OctF_5563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_7522921261 : Nat.Prime 7522921261 := by
  have hfermat : (2 : ZMod 7522921261) ^ (7522921261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 7522921261) ^ ((7522921261 - 1) / 41669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7522921261 (2 : ZMod 7522921261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (17, 1), (59, 1), (41669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (17, 1), (59, 1), (41669, 1)] : List FactorBlock).map factorBlockValue).prod = 7522921261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_59
      · exact prime_free64OctF_41669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_80288119 : Nat.Prime 80288119 := by
  have hfermat : (12 : ZMod 80288119) ^ (80288119 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (12 : ZMod 80288119) ^ ((80288119 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (12 : ZMod 80288119) ^ ((80288119 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (12 : ZMod 80288119) ^ ((80288119 - 1) / 379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (12 : ZMod 80288119) ^ ((80288119 - 1) / 3923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 80288119 (12 : ZMod 80288119)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (379, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (379, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod = 80288119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_379
      · exact prime_free64OctF_3923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_10437455471 : Nat.Prime 10437455471 := by
  have hfermat : (7 : ZMod 10437455471) ^ (10437455471 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 10437455471) ^ ((10437455471 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 10437455471) ^ ((10437455471 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 10437455471) ^ ((10437455471 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 10437455471) ^ ((10437455471 - 1) / 80288119) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10437455471 (7 : ZMod 10437455471)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (80288119, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (80288119, 1)] : List FactorBlock).map factorBlockValue).prod = 10437455471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64OctF_80288119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_15040590709 : Nat.Prime 15040590709 := by
  have hfermat : (14 : ZMod 15040590709) ^ (15040590709 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (14 : ZMod 15040590709) ^ ((15040590709 - 1) / 28183) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15040590709 (14 : ZMod 15040590709)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (13, 1), (311, 1), (28183, 1)] : List FactorBlock).map factorBlockValue).prod = 15040590709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_311
      · exact prime_free64OctF_28183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_16757231 : Nat.Prime 16757231 := by
  have hfermat : (7 : ZMod 16757231) ^ (16757231 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 16757231) ^ ((16757231 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 16757231) ^ ((16757231 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 16757231) ^ ((16757231 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 16757231) ^ ((16757231 - 1) / 239389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16757231 (7 : ZMod 16757231)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (239389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (239389, 1)] : List FactorBlock).map factorBlockValue).prod = 16757231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64OctF_239389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_25940193589 : Nat.Prime 25940193589 := by
  have hfermat : (6 : ZMod 25940193589) ^ (25940193589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 25940193589) ^ ((25940193589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 25940193589) ^ ((25940193589 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 25940193589) ^ ((25940193589 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 25940193589) ^ ((25940193589 - 1) / 16757231) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25940193589 (6 : ZMod 25940193589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (43, 1), (16757231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (43, 1), (16757231, 1)] : List FactorBlock).map factorBlockValue).prod = 25940193589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_free64OctF_16757231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_30384297329 : Nat.Prime 30384297329 := by
  have hfermat : (3 : ZMod 30384297329) ^ (30384297329 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 30384297329) ^ ((30384297329 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 30384297329) ^ ((30384297329 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 30384297329) ^ ((30384297329 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 30384297329) ^ ((30384297329 - 1) / 1709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 30384297329) ^ ((30384297329 - 1) / 14431) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 30384297329 (3 : ZMod 30384297329)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (11, 1), (1709, 1), (14431, 1)] : List FactorBlock).map factorBlockValue).prod = 30384297329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64OctF_1709
      · exact prime_free64OctF_14431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_49159833409 : Nat.Prime 49159833409 := by
  have hfermat : (13 : ZMod 49159833409) ^ (49159833409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 49159833409) ^ ((49159833409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 49159833409) ^ ((49159833409 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 49159833409) ^ ((49159833409 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 49159833409) ^ ((49159833409 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 49159833409) ^ ((49159833409 - 1) / 118373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 49159833409 (13 : ZMod 49159833409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 2), (7, 1), (103, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 2), (7, 1), (103, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod = 49159833409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_103
      · exact prime_free64OctF_118373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_57769814959 : Nat.Prime 57769814959 := by
  have hfermat : (3 : ZMod 57769814959) ^ (57769814959 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 57769814959) ^ ((57769814959 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 57769814959) ^ ((57769814959 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 57769814959) ^ ((57769814959 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 57769814959) ^ ((57769814959 - 1) / 383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 57769814959) ^ ((57769814959 - 1) / 810941) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 57769814959 (3 : ZMod 57769814959)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (31, 1), (383, 1), (810941, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (31, 1), (383, 1), (810941, 1)] : List FactorBlock).map factorBlockValue).prod = 57769814959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_383
      · exact prime_free64OctF_810941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_64859654689 : Nat.Prime 64859654689 := by
  have hfermat : (13 : ZMod 64859654689) ^ (64859654689 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 64859654689) ^ ((64859654689 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 64859654689) ^ ((64859654689 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 64859654689) ^ ((64859654689 - 1) / 13291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 64859654689) ^ ((64859654689 - 1) / 50833) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 64859654689 (13 : ZMod 64859654689)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (13291, 1), (50833, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (13291, 1), (50833, 1)] : List FactorBlock).map factorBlockValue).prod = 64859654689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_13291
      · exact prime_free64OctF_50833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_33107719 : Nat.Prime 33107719 := by
  have hfermat : (7 : ZMod 33107719) ^ (33107719 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 33107719) ^ ((33107719 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 33107719) ^ ((33107719 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 33107719) ^ ((33107719 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 33107719) ^ ((33107719 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 33107719) ^ ((33107719 - 1) / 34273) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 33107719 (7 : ZMod 33107719)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (23, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (23, 1), (34273, 1)] : List FactorBlock).map factorBlockValue).prod = 33107719 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_free64OctF_34273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_69857287091 : Nat.Prime 69857287091 := by
  have hfermat : (2 : ZMod 69857287091) ^ (69857287091 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 69857287091) ^ ((69857287091 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 69857287091) ^ ((69857287091 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 69857287091) ^ ((69857287091 - 1) / 211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 69857287091) ^ ((69857287091 - 1) / 33107719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 69857287091 (2 : ZMod 69857287091)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (211, 1), (33107719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (211, 1), (33107719, 1)] : List FactorBlock).map factorBlockValue).prod = 69857287091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_211
      · exact prime_free64OctF_33107719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_160736592539 : Nat.Prime 160736592539 := by
  have hfermat : (2 : ZMod 160736592539) ^ (160736592539 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 160736592539) ^ ((160736592539 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 160736592539) ^ ((160736592539 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 160736592539) ^ ((160736592539 - 1) / 49627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 160736592539) ^ ((160736592539 - 1) / 55843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 160736592539 (2 : ZMod 160736592539)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 1), (49627, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod = 160736592539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_free64OctF_49627
      · exact prime_free64OctF_55843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_321473185079 : Nat.Prime 321473185079 := by
  have hfermat : (7 : ZMod 321473185079) ^ (321473185079 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 321473185079) ^ ((321473185079 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 321473185079) ^ ((321473185079 - 1) / 160736592539) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 321473185079 (7 : ZMod 321473185079)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (160736592539, 1)] : List FactorBlock).map factorBlockValue).prod = 321473185079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_160736592539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_144038591 : Nat.Prime 144038591 := by
  have hfermat : (7 : ZMod 144038591) ^ (144038591 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 144038591) ^ ((144038591 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 144038591) ^ ((144038591 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 144038591) ^ ((144038591 - 1) / 827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 144038591) ^ ((144038591 - 1) / 17417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 144038591 (7 : ZMod 144038591)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (827, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod = 144038591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_827
      · exact prime_free64OctF_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_390056504429 : Nat.Prime 390056504429 := by
  have hfermat : (2 : ZMod 390056504429) ^ (390056504429 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 390056504429) ^ ((390056504429 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 390056504429) ^ ((390056504429 - 1) / 677) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 390056504429) ^ ((390056504429 - 1) / 144038591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 390056504429 (2 : ZMod 390056504429)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (677, 1), (144038591, 1)] : List FactorBlock).map factorBlockValue).prod = 390056504429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_677
      · exact prime_free64OctF_144038591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_400597142329 : Nat.Prime 400597142329 := by
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
      · exact prime_free64OctF_7982567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_158385407 : Nat.Prime 158385407 := by
  have hfermat : (5 : ZMod 158385407) ^ (158385407 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 158385407) ^ ((158385407 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 158385407) ^ ((158385407 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 158385407) ^ ((158385407 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 158385407) ^ ((158385407 - 1) / 181219) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 158385407 (5 : ZMod 158385407)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (23, 1), (181219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (23, 1), (181219, 1)] : List FactorBlock).map factorBlockValue).prod = 158385407 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_free64OctF_181219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_545479341709 : Nat.Prime 545479341709 := by
  have hfermat : (10 : ZMod 545479341709) ^ (545479341709 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 545479341709) ^ ((545479341709 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 545479341709) ^ ((545479341709 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 545479341709) ^ ((545479341709 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 545479341709) ^ ((545479341709 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 545479341709) ^ ((545479341709 - 1) / 158385407) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 545479341709 (10 : ZMod 545479341709)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (41, 1), (158385407, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (41, 1), (158385407, 1)] : List FactorBlock).map factorBlockValue).prod = 545479341709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_41
      · exact prime_free64OctF_158385407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_850971844357 : Nat.Prime 850971844357 := by
  have hfermat : (2 : ZMod 850971844357) ^ (850971844357 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 850971844357) ^ ((850971844357 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 850971844357) ^ ((850971844357 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 850971844357) ^ ((850971844357 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 850971844357) ^ ((850971844357 - 1) / 1489) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 850971844357) ^ ((850971844357 - 1) / 1107569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 850971844357 (2 : ZMod 850971844357)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (1489, 1), (1107569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (1489, 1), (1107569, 1)] : List FactorBlock).map factorBlockValue).prod = 850971844357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_free64OctF_1489
      · exact prime_free64OctF_1107569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1656564227 : Nat.Prime 1656564227 := by
  have hfermat : (2 : ZMod 1656564227) ^ (1656564227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1656564227) ^ ((1656564227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1656564227) ^ ((1656564227 - 1) / 101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1656564227) ^ ((1656564227 - 1) / 2521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1656564227) ^ ((1656564227 - 1) / 3253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1656564227 (2 : ZMod 1656564227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (101, 1), (2521, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod = 1656564227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_101
      · exact prime_free64OctF_2521
      · exact prime_free64OctF_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1272241326337 : Nat.Prime 1272241326337 := by
  have hfermat : (5 : ZMod 1272241326337) ^ (1272241326337 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1272241326337) ^ ((1272241326337 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1272241326337) ^ ((1272241326337 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1272241326337) ^ ((1272241326337 - 1) / 1656564227) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1272241326337 (5 : ZMod 1272241326337)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (1656564227, 1)] : List FactorBlock).map factorBlockValue).prod = 1272241326337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_1656564227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1357034643673 : Nat.Prime 1357034643673 := by
  have hfermat : (5 : ZMod 1357034643673) ^ (1357034643673 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1357034643673) ^ ((1357034643673 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1357034643673) ^ ((1357034643673 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1357034643673) ^ ((1357034643673 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 1357034643673) ^ ((1357034643673 - 1) / 2269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 1357034643673) ^ ((1357034643673 - 1) / 300239) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1357034643673 (5 : ZMod 1357034643673)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (83, 1), (2269, 1), (300239, 1)] : List FactorBlock).map factorBlockValue).prod = 1357034643673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_free64OctF_2269
      · exact prime_free64OctF_300239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_128549537 : Nat.Prime 128549537 := by
  have hfermat : (3 : ZMod 128549537) ^ (128549537 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 128549537) ^ ((128549537 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 128549537) ^ ((128549537 - 1) / 4017173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 128549537 (3 : ZMod 128549537)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (4017173, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (4017173, 1)] : List FactorBlock).map factorBlockValue).prod = 128549537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_4017173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_695967193319 : Nat.Prime 695967193319 := by
  have hfermat : (13 : ZMod 695967193319) ^ (695967193319 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 695967193319) ^ ((695967193319 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 695967193319) ^ ((695967193319 - 1) / 2707) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 695967193319) ^ ((695967193319 - 1) / 128549537) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 695967193319 (13 : ZMod 695967193319)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2707, 1), (128549537, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2707, 1), (128549537, 1)] : List FactorBlock).map factorBlockValue).prod = 695967193319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_2707
      · exact prime_free64OctF_128549537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1391934386639 : Nat.Prime 1391934386639 := by
  have hfermat : (11 : ZMod 1391934386639) ^ (1391934386639 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 1391934386639) ^ ((1391934386639 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 1391934386639) ^ ((1391934386639 - 1) / 695967193319) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1391934386639 (11 : ZMod 1391934386639)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (695967193319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (695967193319, 1)] : List FactorBlock).map factorBlockValue).prod = 1391934386639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_695967193319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_3256364927 : Nat.Prime 3256364927 := by
  have hfermat : (5 : ZMod 3256364927) ^ (3256364927 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 3256364927) ^ ((3256364927 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 3256364927) ^ ((3256364927 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 3256364927) ^ ((3256364927 - 1) / 419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 3256364927) ^ ((3256364927 - 1) / 228581) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3256364927 (5 : ZMod 3256364927)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (419, 1), (228581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (419, 1), (228581, 1)] : List FactorBlock).map factorBlockValue).prod = 3256364927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64OctF_419
      · exact prime_free64OctF_228581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1432800567881 : Nat.Prime 1432800567881 := by
  have hfermat : (6 : ZMod 1432800567881) ^ (1432800567881 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1432800567881) ^ ((1432800567881 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1432800567881) ^ ((1432800567881 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1432800567881) ^ ((1432800567881 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1432800567881) ^ ((1432800567881 - 1) / 3256364927) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1432800567881 (6 : ZMod 1432800567881)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (11, 1), (3256364927, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (11, 1), (3256364927, 1)] : List FactorBlock).map factorBlockValue).prod = 1432800567881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64OctF_3256364927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_25331881 : Nat.Prime 25331881 := by
  have hfermat : (17 : ZMod 25331881) ^ (25331881 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (17 : ZMod 25331881) ^ ((25331881 - 1) / 569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25331881 (17 : ZMod 25331881)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7, 1), (53, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod = 25331881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_free64OctF_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_10892708831 : Nat.Prime 10892708831 := by
  have hfermat : (7 : ZMod 10892708831) ^ (10892708831 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 10892708831) ^ ((10892708831 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 10892708831) ^ ((10892708831 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 10892708831) ^ ((10892708831 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 10892708831) ^ ((10892708831 - 1) / 25331881) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10892708831 (7 : ZMod 10892708831)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (43, 1), (25331881, 1)] : List FactorBlock).map factorBlockValue).prod = 10892708831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_free64OctF_25331881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1982473007243 : Nat.Prime 1982473007243 := by
  have hfermat : (2 : ZMod 1982473007243) ^ (1982473007243 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1982473007243) ^ ((1982473007243 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1982473007243) ^ ((1982473007243 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1982473007243) ^ ((1982473007243 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1982473007243) ^ ((1982473007243 - 1) / 10892708831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1982473007243 (2 : ZMod 1982473007243)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (13, 1), (10892708831, 1)] : List FactorBlock).map factorBlockValue).prod = 1982473007243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_free64OctF_10892708831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_10600781 : Nat.Prime 10600781 := by
  have hfermat : (2 : ZMod 10600781) ^ (10600781 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 10600781) ^ ((10600781 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 10600781) ^ ((10600781 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 10600781) ^ ((10600781 - 1) / 421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 10600781) ^ ((10600781 - 1) / 1259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10600781 (2 : ZMod 10600781)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (421, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (421, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod = 10600781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_421
      · exact prime_free64OctF_1259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_2017561841483 : Nat.Prime 2017561841483 := by
  have hfermat : (2 : ZMod 2017561841483) ^ (2017561841483 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2017561841483) ^ ((2017561841483 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2017561841483) ^ ((2017561841483 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2017561841483) ^ ((2017561841483 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2017561841483) ^ ((2017561841483 - 1) / 211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2017561841483) ^ ((2017561841483 - 1) / 10600781) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2017561841483 (2 : ZMod 2017561841483)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (41, 1), (211, 1), (10600781, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (41, 1), (211, 1), (10600781, 1)] : List FactorBlock).map factorBlockValue).prod = 2017561841483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_41
      · exact prime_free64OctF_211
      · exact prime_free64OctF_10600781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_2192745608479 : Nat.Prime 2192745608479 := by
  have hfermat : (6 : ZMod 2192745608479) ^ (2192745608479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 2192745608479) ^ ((2192745608479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 2192745608479) ^ ((2192745608479 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 2192745608479) ^ ((2192745608479 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 2192745608479) ^ ((2192745608479 - 1) / 9739) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 2192745608479) ^ ((2192745608479 - 1) / 60427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2192745608479 (6 : ZMod 2192745608479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 4), (23, 1), (9739, 1), (60427, 1)] : List FactorBlock).map factorBlockValue).prod = 2192745608479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_free64OctF_9739
      · exact prime_free64OctF_60427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_2943508165337 : Nat.Prime 2943508165337 := by
  have hfermat : (3 : ZMod 2943508165337) ^ (2943508165337 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2943508165337) ^ ((2943508165337 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2943508165337) ^ ((2943508165337 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2943508165337) ^ ((2943508165337 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2943508165337) ^ ((2943508165337 - 1) / 509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 2943508165337) ^ ((2943508165337 - 1) / 231169) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2943508165337 (3 : ZMod 2943508165337)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (53, 1), (59, 1), (509, 1), (231169, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (53, 1), (59, 1), (509, 1), (231169, 1)] : List FactorBlock).map factorBlockValue).prod = 2943508165337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_t64_59
      · exact prime_free64OctF_509
      · exact prime_free64OctF_231169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_536838309149 : Nat.Prime 536838309149 := by
  have hfermat : (2 : ZMod 536838309149) ^ (536838309149 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 536838309149) ^ ((536838309149 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 536838309149) ^ ((536838309149 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 536838309149) ^ ((536838309149 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 536838309149) ^ ((536838309149 - 1) / 283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 536838309149) ^ ((536838309149 - 1) / 73651) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 536838309149 (2 : ZMod 536838309149)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (47, 1), (137, 1), (283, 1), (73651, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (47, 1), (137, 1), (283, 1), (73651, 1)] : List FactorBlock).map factorBlockValue).prod = 536838309149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_47
      · exact prime_t64_137
      · exact prime_t64_283
      · exact prime_free64OctF_73651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_4294706473193 : Nat.Prime 4294706473193 := by
  have hfermat : (3 : ZMod 4294706473193) ^ (4294706473193 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4294706473193) ^ ((4294706473193 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4294706473193) ^ ((4294706473193 - 1) / 536838309149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4294706473193 (3 : ZMod 4294706473193)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (536838309149, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (536838309149, 1)] : List FactorBlock).map factorBlockValue).prod = 4294706473193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_536838309149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_76085543257 : Nat.Prime 76085543257 := by
  have hfermat : (5 : ZMod 76085543257) ^ (76085543257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 76085543257) ^ ((76085543257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 76085543257) ^ ((76085543257 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 76085543257) ^ ((76085543257 - 1) / 2221) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 76085543257) ^ ((76085543257 - 1) / 1427389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 76085543257 (5 : ZMod 76085543257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2221, 1), (1427389, 1)] : List FactorBlock).map factorBlockValue).prod = 76085543257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_2221
      · exact prime_free64OctF_1427389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_5934672374047 : Nat.Prime 5934672374047 := by
  have hfermat : (3 : ZMod 5934672374047) ^ (5934672374047 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 5934672374047) ^ ((5934672374047 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 5934672374047) ^ ((5934672374047 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 5934672374047) ^ ((5934672374047 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 5934672374047) ^ ((5934672374047 - 1) / 76085543257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5934672374047 (3 : ZMod 5934672374047)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (76085543257, 1)] : List FactorBlock).map factorBlockValue).prod = 5934672374047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64OctF_76085543257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_7280697974663 : Nat.Prime 7280697974663 := by
  have hfermat : (5 : ZMod 7280697974663) ^ (7280697974663 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 7280697974663) ^ ((7280697974663 - 1) / 3696923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7280697974663 (5 : ZMod 7280697974663)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (41, 1), (47, 1), (73, 1), (3696923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (41, 1), (47, 1), (73, 1), (3696923, 1)] : List FactorBlock).map factorBlockValue).prod = 7280697974663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_41
      · exact prime_t64_47
      · exact prime_t64_73
      · exact prime_free64OctF_3696923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_11680677399577 : Nat.Prime 11680677399577 := by
  have hfermat : (5 : ZMod 11680677399577) ^ (11680677399577 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 11680677399577) ^ ((11680677399577 - 1) / 674701) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11680677399577 (5 : ZMod 11680677399577)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (23, 1), (79, 1), (397, 1), (674701, 1)] : List FactorBlock).map factorBlockValue).prod = 11680677399577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_t64_79
      · exact prime_free64OctF_397
      · exact prime_free64OctF_674701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_7647016217 : Nat.Prime 7647016217 := by
  have hfermat : (3 : ZMod 7647016217) ^ (7647016217 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 7647016217) ^ ((7647016217 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 7647016217) ^ ((7647016217 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 7647016217) ^ ((7647016217 - 1) / 7549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 7647016217) ^ ((7647016217 - 1) / 18089) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7647016217 (3 : ZMod 7647016217)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (7549, 1), (18089, 1)] : List FactorBlock).map factorBlockValue).prod = 7647016217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64OctF_7549
      · exact prime_free64OctF_18089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_13443454509487 : Nat.Prime 13443454509487 := by
  have hfermat : (3 : ZMod 13443454509487) ^ (13443454509487 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 13443454509487) ^ ((13443454509487 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 13443454509487) ^ ((13443454509487 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 13443454509487) ^ ((13443454509487 - 1) / 293) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 13443454509487) ^ ((13443454509487 - 1) / 7647016217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13443454509487 (3 : ZMod 13443454509487)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (293, 1), (7647016217, 1)] : List FactorBlock).map factorBlockValue).prod = 13443454509487 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_293
      · exact prime_free64OctF_7647016217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_10415057532713 : Nat.Prime 10415057532713 := by
  have hfermat : (3 : ZMod 10415057532713) ^ (10415057532713 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10415057532713) ^ ((10415057532713 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10415057532713) ^ ((10415057532713 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10415057532713) ^ ((10415057532713 - 1) / 101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10415057532713) ^ ((10415057532713 - 1) / 1559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 10415057532713) ^ ((10415057532713 - 1) / 1181153) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10415057532713 (3 : ZMod 10415057532713)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (101, 1), (1559, 1), (1181153, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (101, 1), (1559, 1), (1181153, 1)] : List FactorBlock).map factorBlockValue).prod = 10415057532713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_101
      · exact prime_free64OctF_1559
      · exact prime_free64OctF_1181153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_20830115065427 : Nat.Prime 20830115065427 := by
  have hfermat : (2 : ZMod 20830115065427) ^ (20830115065427 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 20830115065427) ^ ((20830115065427 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 20830115065427) ^ ((20830115065427 - 1) / 10415057532713) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20830115065427 (2 : ZMod 20830115065427)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (10415057532713, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (10415057532713, 1)] : List FactorBlock).map factorBlockValue).prod = 20830115065427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_10415057532713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_2020679827 : Nat.Prime 2020679827 := by
  have hfermat : (2 : ZMod 2020679827) ^ (2020679827 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2020679827) ^ ((2020679827 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2020679827) ^ ((2020679827 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2020679827) ^ ((2020679827 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2020679827) ^ ((2020679827 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2020679827) ^ ((2020679827 - 1) / 155413) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2020679827 (2 : ZMod 2020679827)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (197, 1), (155413, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (197, 1), (155413, 1)] : List FactorBlock).map factorBlockValue).prod = 2020679827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_197
      · exact prime_free64OctF_155413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_48496315849 : Nat.Prime 48496315849 := by
  have hfermat : (26 : ZMod 48496315849) ^ (48496315849 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (26 : ZMod 48496315849) ^ ((48496315849 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (26 : ZMod 48496315849) ^ ((48496315849 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (26 : ZMod 48496315849) ^ ((48496315849 - 1) / 2020679827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 48496315849 (26 : ZMod 48496315849)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2020679827, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2020679827, 1)] : List FactorBlock).map factorBlockValue).prod = 48496315849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_2020679827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_27351922138837 : Nat.Prime 27351922138837 := by
  have hfermat : (2 : ZMod 27351922138837) ^ (27351922138837 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 27351922138837) ^ ((27351922138837 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 27351922138837) ^ ((27351922138837 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 27351922138837) ^ ((27351922138837 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 27351922138837) ^ ((27351922138837 - 1) / 48496315849) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 27351922138837 (2 : ZMod 27351922138837)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (47, 1), (48496315849, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (47, 1), (48496315849, 1)] : List FactorBlock).map factorBlockValue).prod = 27351922138837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_free64OctF_48496315849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_4829555736107 : Nat.Prime 4829555736107 := by
  have hfermat : (2 : ZMod 4829555736107) ^ (4829555736107 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4829555736107) ^ ((4829555736107 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4829555736107) ^ ((4829555736107 - 1) / 1733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4829555736107) ^ ((4829555736107 - 1) / 25373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 4829555736107) ^ ((4829555736107 - 1) / 54917) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4829555736107 (2 : ZMod 4829555736107)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1733, 1), (25373, 1), (54917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1733, 1), (25373, 1), (54917, 1)] : List FactorBlock).map factorBlockValue).prod = 4829555736107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_1733
      · exact prime_free64OctF_25373
      · exact prime_free64OctF_54917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_38636445888857 : Nat.Prime 38636445888857 := by
  have hfermat : (3 : ZMod 38636445888857) ^ (38636445888857 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 38636445888857) ^ ((38636445888857 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 38636445888857) ^ ((38636445888857 - 1) / 4829555736107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 38636445888857 (3 : ZMod 38636445888857)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (4829555736107, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (4829555736107, 1)] : List FactorBlock).map factorBlockValue).prod = 38636445888857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_4829555736107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_289267687 : Nat.Prime 289267687 := by
  have hfermat : (5 : ZMod 289267687) ^ (289267687 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 289267687) ^ ((289267687 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 289267687) ^ ((289267687 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 289267687) ^ ((289267687 - 1) / 595201) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 289267687 (5 : ZMod 289267687)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 5), (595201, 1)] : List FactorBlock).map factorBlockValue).prod = 289267687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_595201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_159097227851 : Nat.Prime 159097227851 := by
  have hfermat : (6 : ZMod 159097227851) ^ (159097227851 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 159097227851) ^ ((159097227851 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 159097227851) ^ ((159097227851 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 159097227851) ^ ((159097227851 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 159097227851) ^ ((159097227851 - 1) / 289267687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 159097227851 (6 : ZMod 159097227851)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (11, 1), (289267687, 1)] : List FactorBlock).map factorBlockValue).prod = 159097227851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64OctF_289267687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_45820001621089 : Nat.Prime 45820001621089 := by
  have hfermat : (13 : ZMod 45820001621089) ^ (45820001621089 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 45820001621089) ^ ((45820001621089 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 45820001621089) ^ ((45820001621089 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 45820001621089) ^ ((45820001621089 - 1) / 159097227851) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 45820001621089 (13 : ZMod 45820001621089)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (159097227851, 1)] : List FactorBlock).map factorBlockValue).prod = 45820001621089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_159097227851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_277100209 : Nat.Prime 277100209 := by
  have hfermat : (17 : ZMod 277100209) ^ (277100209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (17 : ZMod 277100209) ^ ((277100209 - 1) / 373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 277100209 (17 : ZMod 277100209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (7, 1), (11, 1), (67, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod = 277100209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_67
      · exact prime_free64OctF_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_60421700572451 : Nat.Prime 60421700572451 := by
  have hfermat : (2 : ZMod 60421700572451) ^ (60421700572451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 60421700572451) ^ ((60421700572451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 60421700572451) ^ ((60421700572451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 60421700572451) ^ ((60421700572451 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 60421700572451) ^ ((60421700572451 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 60421700572451) ^ ((60421700572451 - 1) / 277100209) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 60421700572451 (2 : ZMod 60421700572451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 2), (89, 1), (277100209, 1)] : List FactorBlock).map factorBlockValue).prod = 60421700572451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_free64OctF_277100209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_297806723575661 : Nat.Prime 297806723575661 := by
  have hfermat : (2 : ZMod 297806723575661) ^ (297806723575661 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 541) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 7477) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 297806723575661) ^ ((297806723575661 - 1) / 283163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 297806723575661 (2 : ZMod 297806723575661)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (541, 1), (7477, 1), (283163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (541, 1), (7477, 1), (283163, 1)] : List FactorBlock).map factorBlockValue).prod = 297806723575661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64OctF_541
      · exact prime_free64OctF_7477
      · exact prime_free64OctF_283163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_416726749916363 : Nat.Prime 416726749916363 := by
  have hfermat : (2 : ZMod 416726749916363) ^ (416726749916363 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 416726749916363) ^ ((416726749916363 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 416726749916363) ^ ((416726749916363 - 1) / 4787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 416726749916363) ^ ((416726749916363 - 1) / 8839) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 416726749916363) ^ ((416726749916363 - 1) / 4924417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 416726749916363 (2 : ZMod 416726749916363)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (4787, 1), (8839, 1), (4924417, 1)] : List FactorBlock).map factorBlockValue).prod = 416726749916363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_4787
      · exact prime_free64OctF_8839
      · exact prime_free64OctF_4924417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_2024581991983 : Nat.Prime 2024581991983 := by
  have hfermat : (3 : ZMod 2024581991983) ^ (2024581991983 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2024581991983) ^ ((2024581991983 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2024581991983) ^ ((2024581991983 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2024581991983) ^ ((2024581991983 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2024581991983) ^ ((2024581991983 - 1) / 6997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 2024581991983) ^ ((2024581991983 - 1) / 4384091) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2024581991983 (3 : ZMod 2024581991983)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (6997, 1), (4384091, 1)] : List FactorBlock).map factorBlockValue).prod = 2024581991983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64OctF_6997
      · exact prime_free64OctF_4384091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_700505369226119 : Nat.Prime 700505369226119 := by
  have hfermat : (7 : ZMod 700505369226119) ^ (700505369226119 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 700505369226119) ^ ((700505369226119 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 700505369226119) ^ ((700505369226119 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 700505369226119) ^ ((700505369226119 - 1) / 2024581991983) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 700505369226119 (7 : ZMod 700505369226119)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (173, 1), (2024581991983, 1)] : List FactorBlock).map factorBlockValue).prod = 700505369226119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_173
      · exact prime_free64OctF_2024581991983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1088621057 : Nat.Prime 1088621057 := by
  have hfermat : (3 : ZMod 1088621057) ^ (1088621057 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1088621057) ^ ((1088621057 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1088621057) ^ ((1088621057 - 1) / 2126213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1088621057 (3 : ZMod 1088621057)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (2126213, 1)] : List FactorBlock).map factorBlockValue).prod = 1088621057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_2126213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_1276216592026469 : Nat.Prime 1276216592026469 := by
  have hfermat : (2 : ZMod 1276216592026469) ^ (1276216592026469 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1276216592026469) ^ ((1276216592026469 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1276216592026469) ^ ((1276216592026469 - 1) / 293081) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1276216592026469) ^ ((1276216592026469 - 1) / 1088621057) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1276216592026469 (2 : ZMod 1276216592026469)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (293081, 1), (1088621057, 1)] : List FactorBlock).map factorBlockValue).prod = 1276216592026469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_293081
      · exact prime_free64OctF_1088621057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_2351424533 : Nat.Prime 2351424533 := by
  have hfermat : (2 : ZMod 2351424533) ^ (2351424533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2351424533) ^ ((2351424533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2351424533) ^ ((2351424533 - 1) / 491) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2351424533) ^ ((2351424533 - 1) / 1197263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2351424533 (2 : ZMod 2351424533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (491, 1), (1197263, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (491, 1), (1197263, 1)] : List FactorBlock).map factorBlockValue).prod = 2351424533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_491
      · exact prime_free64OctF_1197263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_3093346001652161 : Nat.Prime 3093346001652161 := by
  have hfermat : (3 : ZMod 3093346001652161) ^ (3093346001652161 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3093346001652161) ^ ((3093346001652161 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3093346001652161) ^ ((3093346001652161 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3093346001652161) ^ ((3093346001652161 - 1) / 4111) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3093346001652161) ^ ((3093346001652161 - 1) / 2351424533) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3093346001652161 (3 : ZMod 3093346001652161)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (4111, 1), (2351424533, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (4111, 1), (2351424533, 1)] : List FactorBlock).map factorBlockValue).prod = 3093346001652161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_4111
      · exact prime_free64OctF_2351424533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_151677853 : Nat.Prime 151677853 := by
  have hfermat : (2 : ZMod 151677853) ^ (151677853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 151677853) ^ ((151677853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 151677853) ^ ((151677853 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 151677853) ^ ((151677853 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 151677853) ^ ((151677853 - 1) / 152287) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 151677853 (2 : ZMod 151677853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (83, 1), (152287, 1)] : List FactorBlock).map factorBlockValue).prod = 151677853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_83
      · exact prime_free64OctF_152287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_4496625855541289 : Nat.Prime 4496625855541289 := by
  have hfermat : (3 : ZMod 4496625855541289) ^ (4496625855541289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4496625855541289) ^ ((4496625855541289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4496625855541289) ^ ((4496625855541289 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4496625855541289) ^ ((4496625855541289 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4496625855541289) ^ ((4496625855541289 - 1) / 23017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 4496625855541289) ^ ((4496625855541289 - 1) / 151677853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4496625855541289 (3 : ZMod 4496625855541289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (23, 1), (23017, 1), (151677853, 1)] : List FactorBlock).map factorBlockValue).prod = 4496625855541289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_free64OctF_23017
      · exact prime_free64OctF_151677853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_72158159 : Nat.Prime 72158159 := by
  have hfermat : (13 : ZMod 72158159) ^ (72158159 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 72158159) ^ ((72158159 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 72158159) ^ ((72158159 - 1) / 1901) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 72158159) ^ ((72158159 - 1) / 18979) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 72158159 (13 : ZMod 72158159)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (1901, 1), (18979, 1)] : List FactorBlock).map factorBlockValue).prod = 72158159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_1901
      · exact prime_free64OctF_18979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_20000838920189041 : Nat.Prime 20000838920189041 := by
  have hfermat : (7 : ZMod 20000838920189041) ^ (20000838920189041 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 20000838920189041) ^ ((20000838920189041 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 20000838920189041) ^ ((20000838920189041 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 20000838920189041) ^ ((20000838920189041 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 20000838920189041) ^ ((20000838920189041 - 1) / 384973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 20000838920189041) ^ ((20000838920189041 - 1) / 72158159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20000838920189041 (7 : ZMod 20000838920189041)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (5, 1), (384973, 1), (72158159, 1)] : List FactorBlock).map factorBlockValue).prod = 20000838920189041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_384973
      · exact prime_free64OctF_72158159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_54302271113539481 : Nat.Prime 54302271113539481 := by
  have hfermat : (3 : ZMod 54302271113539481) ^ (54302271113539481 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 1109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 2281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 54302271113539481) ^ ((54302271113539481 - 1) / 265543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 54302271113539481 (3 : ZMod 54302271113539481)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (43, 1), (47, 1), (1109, 1), (2281, 1), (265543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (43, 1), (47, 1), (1109, 1), (2281, 1), (265543, 1)] : List FactorBlock).map factorBlockValue).prod = 54302271113539481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_free64OctF_1109
      · exact prime_t64_2281
      · exact prime_free64OctF_265543
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

private theorem prime_free64OctF_73753679 : Nat.Prime 73753679 := by
  have hfermat : (17 : ZMod 73753679) ^ (73753679 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 73753679) ^ ((73753679 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 73753679) ^ ((73753679 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 73753679) ^ ((73753679 - 1) / 359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 73753679) ^ ((73753679 - 1) / 739) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73753679 (17 : ZMod 73753679)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 1), (359, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 1), (359, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod = 73753679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_free64OctF_359
      · exact prime_free64OctF_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_72807849429885929 : Nat.Prime 72807849429885929 := by
  have hfermat : (3 : ZMod 72807849429885929) ^ (72807849429885929 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 72807849429885929) ^ ((72807849429885929 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 72807849429885929) ^ ((72807849429885929 - 1) / 373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 72807849429885929) ^ ((72807849429885929 - 1) / 330823) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 72807849429885929) ^ ((72807849429885929 - 1) / 73753679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 72807849429885929 (3 : ZMod 72807849429885929)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (373, 1), (330823, 1), (73753679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (373, 1), (330823, 1), (73753679, 1)] : List FactorBlock).map factorBlockValue).prod = 72807849429885929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_373
      · exact prime_free64OctF_330823
      · exact prime_free64OctF_73753679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_23959559521 : Nat.Prime 23959559521 := by
  have hfermat : (11 : ZMod 23959559521) ^ (23959559521 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 23959559521) ^ ((23959559521 - 1) / 6701) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 23959559521 (11 : ZMod 23959559521)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 1), (13, 1), (191, 1), (6701, 1)] : List FactorBlock).map factorBlockValue).prod = 23959559521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_191
      · exact prime_free64OctF_6701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_85512338798115589 : Nat.Prime 85512338798115589 := by
  have hfermat : (6 : ZMod 85512338798115589) ^ (85512338798115589 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 85512338798115589) ^ ((85512338798115589 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 85512338798115589) ^ ((85512338798115589 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 85512338798115589) ^ ((85512338798115589 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 85512338798115589) ^ ((85512338798115589 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 85512338798115589) ^ ((85512338798115589 - 1) / 23959559521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 85512338798115589 (6 : ZMod 85512338798115589)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (59, 1), (71, 2), (23959559521, 1)] : List FactorBlock).map factorBlockValue).prod = 85512338798115589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_59
      · exact prime_t64_71
      · exact prime_free64OctF_23959559521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_171113017 : Nat.Prime 171113017 := by
  have hfermat : (5 : ZMod 171113017) ^ (171113017 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 171113017) ^ ((171113017 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 171113017) ^ ((171113017 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 171113017) ^ ((171113017 - 1) / 367) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 171113017) ^ ((171113017 - 1) / 19427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 171113017 (5 : ZMod 171113017)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (367, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (367, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod = 171113017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_367
      · exact prime_free64OctF_19427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_168618696733348423 : Nat.Prime 168618696733348423 := by
  have hfermat : (3 : ZMod 168618696733348423) ^ (168618696733348423 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 953) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 15667) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 168618696733348423) ^ ((168618696733348423 - 1) / 171113017) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 168618696733348423 (3 : ZMod 168618696733348423)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (953, 1), (15667, 1), (171113017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (953, 1), (15667, 1), (171113017, 1)] : List FactorBlock).map factorBlockValue).prod = 168618696733348423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64OctF_953
      · exact prime_free64OctF_15667
      · exact prime_free64OctF_171113017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_41734093 : Nat.Prime 41734093 := by
  have hfermat : (2 : ZMod 41734093) ^ (41734093 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 41734093) ^ ((41734093 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 41734093) ^ ((41734093 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 41734093) ^ ((41734093 - 1) / 3477841) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 41734093 (2 : ZMod 41734093)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (3477841, 1)] : List FactorBlock).map factorBlockValue).prod = 41734093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_3477841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_82299631397 : Nat.Prime 82299631397 := by
  have hfermat : (2 : ZMod 82299631397) ^ (82299631397 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 82299631397) ^ ((82299631397 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 82299631397) ^ ((82299631397 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 82299631397) ^ ((82299631397 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 82299631397) ^ ((82299631397 - 1) / 41734093) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 82299631397 (2 : ZMod 82299631397)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (29, 1), (41734093, 1)] : List FactorBlock).map factorBlockValue).prod = 82299631397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_29
      · exact prime_free64OctF_41734093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_493797788383 : Nat.Prime 493797788383 := by
  have hfermat : (3 : ZMod 493797788383) ^ (493797788383 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 493797788383) ^ ((493797788383 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 493797788383) ^ ((493797788383 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 493797788383) ^ ((493797788383 - 1) / 82299631397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 493797788383 (3 : ZMod 493797788383)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (82299631397, 1)] : List FactorBlock).map factorBlockValue).prod = 493797788383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_82299631397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_4937977883831 : Nat.Prime 4937977883831 := by
  have hfermat : (11 : ZMod 4937977883831) ^ (4937977883831 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 4937977883831) ^ ((4937977883831 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 4937977883831) ^ ((4937977883831 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 4937977883831) ^ ((4937977883831 - 1) / 493797788383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4937977883831 (11 : ZMod 4937977883831)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (493797788383, 1)] : List FactorBlock).map factorBlockValue).prod = 4937977883831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_493797788383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_190813341386997503 : Nat.Prime 190813341386997503 := by
  have hfermat : (5 : ZMod 190813341386997503) ^ (190813341386997503 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 190813341386997503) ^ ((190813341386997503 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 190813341386997503) ^ ((190813341386997503 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 190813341386997503) ^ ((190813341386997503 - 1) / 4937977883831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 190813341386997503 (5 : ZMod 190813341386997503)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (139, 2), (4937977883831, 1)] : List FactorBlock).map factorBlockValue).prod = 190813341386997503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_free64OctF_4937977883831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_43273561 : Nat.Prime 43273561 := by
  have hfermat : (13 : ZMod 43273561) ^ (43273561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 43273561) ^ ((43273561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 43273561) ^ ((43273561 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 43273561) ^ ((43273561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 43273561) ^ ((43273561 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 43273561) ^ ((43273561 - 1) / 32783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 43273561 (13 : ZMod 43273561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (11, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (11, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod = 43273561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64OctF_32783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_19386555329 : Nat.Prime 19386555329 := by
  have hfermat : (3 : ZMod 19386555329) ^ (19386555329 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 19386555329) ^ ((19386555329 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 19386555329) ^ ((19386555329 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 19386555329) ^ ((19386555329 - 1) / 43273561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19386555329 (3 : ZMod 19386555329)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (7, 1), (43273561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (7, 1), (43273561, 1)] : List FactorBlock).map factorBlockValue).prod = 19386555329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64OctF_43273561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_357919120937944987 : Nat.Prime 357919120937944987 := by
  have hfermat : (2 : ZMod 357919120937944987) ^ (357919120937944987 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 357919120937944987) ^ ((357919120937944987 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 357919120937944987) ^ ((357919120937944987 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 357919120937944987) ^ ((357919120937944987 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 357919120937944987) ^ ((357919120937944987 - 1) / 439577) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 357919120937944987) ^ ((357919120937944987 - 1) / 19386555329) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 357919120937944987 (2 : ZMod 357919120937944987)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (439577, 1), (19386555329, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (439577, 1), (19386555329, 1)] : List FactorBlock).map factorBlockValue).prod = 357919120937944987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64OctF_439577
      · exact prime_free64OctF_19386555329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_73483933 : Nat.Prime 73483933 := by
  have hfermat : (2 : ZMod 73483933) ^ (73483933 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 73483933) ^ ((73483933 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 73483933) ^ ((73483933 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 73483933) ^ ((73483933 - 1) / 1879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 73483933) ^ ((73483933 - 1) / 3259) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73483933 (2 : ZMod 73483933)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1879, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1879, 1), (3259, 1)] : List FactorBlock).map factorBlockValue).prod = 73483933 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_1879
      · exact prime_free64OctF_3259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_34914148019994973 : Nat.Prime 34914148019994973 := by
  have hfermat : (14 : ZMod 34914148019994973) ^ (34914148019994973 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 34914148019994973) ^ ((34914148019994973 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 34914148019994973) ^ ((34914148019994973 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 34914148019994973) ^ ((34914148019994973 - 1) / 1033) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 34914148019994973) ^ ((34914148019994973 - 1) / 38329) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 34914148019994973) ^ ((34914148019994973 - 1) / 73483933) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 34914148019994973 (14 : ZMod 34914148019994973)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1033, 1), (38329, 1), (73483933, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1033, 1), (38329, 1), (73483933, 1)] : List FactorBlock).map factorBlockValue).prod = 34914148019994973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_1033
      · exact prime_t64_38329
      · exact prime_free64OctF_73483933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_418969776239939677 : Nat.Prime 418969776239939677 := by
  have hfermat : (6 : ZMod 418969776239939677) ^ (418969776239939677 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 418969776239939677) ^ ((418969776239939677 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 418969776239939677) ^ ((418969776239939677 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 418969776239939677) ^ ((418969776239939677 - 1) / 34914148019994973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 418969776239939677 (6 : ZMod 418969776239939677)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (34914148019994973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (34914148019994973, 1)] : List FactorBlock).map factorBlockValue).prod = 418969776239939677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_34914148019994973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_162590957 : Nat.Prime 162590957 := by
  have hfermat : (2 : ZMod 162590957) ^ (162590957 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 162590957) ^ ((162590957 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 162590957) ^ ((162590957 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 162590957) ^ ((162590957 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 162590957) ^ ((162590957 - 1) / 160663) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 162590957 (2 : ZMod 162590957)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (23, 1), (160663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (23, 1), (160663, 1)] : List FactorBlock).map factorBlockValue).prod = 162590957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_free64OctF_160663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_9755457421 : Nat.Prime 9755457421 := by
  have hfermat : (2 : ZMod 9755457421) ^ (9755457421 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9755457421) ^ ((9755457421 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9755457421) ^ ((9755457421 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9755457421) ^ ((9755457421 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 9755457421) ^ ((9755457421 - 1) / 162590957) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9755457421 (2 : ZMod 9755457421)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (162590957, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (162590957, 1)] : List FactorBlock).map factorBlockValue).prod = 9755457421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_162590957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1055186096695009913 : Nat.Prime 1055186096695009913 := by
  have hfermat : (3 : ZMod 1055186096695009913) ^ (1055186096695009913 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1055186096695009913) ^ ((1055186096695009913 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1055186096695009913) ^ ((1055186096695009913 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1055186096695009913) ^ ((1055186096695009913 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1055186096695009913) ^ ((1055186096695009913 - 1) / 3593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1055186096695009913) ^ ((1055186096695009913 - 1) / 9755457421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1055186096695009913 (3 : ZMod 1055186096695009913)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (53, 1), (71, 1), (3593, 1), (9755457421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (53, 1), (71, 1), (3593, 1), (9755457421, 1)] : List FactorBlock).map factorBlockValue).prod = 1055186096695009913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_t64_71
      · exact prime_free64OctF_3593
      · exact prime_free64OctF_9755457421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_15587213 : Nat.Prime 15587213 := by
  have hfermat : (2 : ZMod 15587213) ^ (15587213 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15587213) ^ ((15587213 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15587213) ^ ((15587213 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15587213) ^ ((15587213 - 1) / 105319) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15587213 (2 : ZMod 15587213)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (37, 1), (105319, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (37, 1), (105319, 1)] : List FactorBlock).map factorBlockValue).prod = 15587213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_free64OctF_105319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_469486855561 : Nat.Prime 469486855561 := by
  have hfermat : (7 : ZMod 469486855561) ^ (469486855561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 469486855561) ^ ((469486855561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 469486855561) ^ ((469486855561 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 469486855561) ^ ((469486855561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 469486855561) ^ ((469486855561 - 1) / 251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 469486855561) ^ ((469486855561 - 1) / 15587213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 469486855561 (7 : ZMod 469486855561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (251, 1), (15587213, 1)] : List FactorBlock).map factorBlockValue).prod = 469486855561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_251
      · exact prime_free64OctF_15587213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1625331568846003853 : Nat.Prime 1625331568846003853 := by
  have hfermat : (2 : ZMod 1625331568846003853) ^ (1625331568846003853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1625331568846003853) ^ ((1625331568846003853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1625331568846003853) ^ ((1625331568846003853 - 1) / 865483) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1625331568846003853) ^ ((1625331568846003853 - 1) / 469486855561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1625331568846003853 (2 : ZMod 1625331568846003853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (865483, 1), (469486855561, 1)] : List FactorBlock).map factorBlockValue).prod = 1625331568846003853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_865483
      · exact prime_free64OctF_469486855561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_143826233 : Nat.Prime 143826233 := by
  have hfermat : (3 : ZMod 143826233) ^ (143826233 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 143826233) ^ ((143826233 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 143826233) ^ ((143826233 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 143826233) ^ ((143826233 - 1) / 563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 143826233) ^ ((143826233 - 1) / 2903) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 143826233 (3 : ZMod 143826233)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (563, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod = 143826233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_563
      · exact prime_free64OctF_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_3030158014634483503 : Nat.Prime 3030158014634483503 := by
  have hfermat : (3 : ZMod 3030158014634483503) ^ (3030158014634483503 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 6514591) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 3030158014634483503) ^ ((3030158014634483503 - 1) / 143826233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3030158014634483503 (3 : ZMod 3030158014634483503)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 2), (11, 1), (6514591, 1), (143826233, 1)] : List FactorBlock).map factorBlockValue).prod = 3030158014634483503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64OctF_6514591
      · exact prime_free64OctF_143826233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_40441811 : Nat.Prime 40441811 := by
  have hfermat : (2 : ZMod 40441811) ^ (40441811 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 40441811) ^ ((40441811 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 40441811) ^ ((40441811 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 40441811) ^ ((40441811 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 40441811) ^ ((40441811 - 1) / 233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 40441811) ^ ((40441811 - 1) / 1021) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 40441811 (2 : ZMod 40441811)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (17, 1), (233, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (17, 1), (233, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod = 40441811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_t64_233
      · exact prime_free64OctF_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_242650867 : Nat.Prime 242650867 := by
  have hfermat : (2 : ZMod 242650867) ^ (242650867 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 242650867) ^ ((242650867 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 242650867) ^ ((242650867 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 242650867) ^ ((242650867 - 1) / 40441811) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 242650867 (2 : ZMod 242650867)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (40441811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (40441811, 1)] : List FactorBlock).map factorBlockValue).prod = 242650867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_40441811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_21838578031 : Nat.Prime 21838578031 := by
  have hfermat : (6 : ZMod 21838578031) ^ (21838578031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 21838578031) ^ ((21838578031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 21838578031) ^ ((21838578031 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 21838578031) ^ ((21838578031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 21838578031) ^ ((21838578031 - 1) / 242650867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21838578031 (6 : ZMod 21838578031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (242650867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (242650867, 1)] : List FactorBlock).map factorBlockValue).prod = 21838578031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_242650867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_4811218253340714821 : Nat.Prime 4811218253340714821 := by
  have hfermat : (3 : ZMod 4811218253340714821) ^ (4811218253340714821 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4811218253340714821) ^ ((4811218253340714821 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4811218253340714821) ^ ((4811218253340714821 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4811218253340714821) ^ ((4811218253340714821 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4811218253340714821) ^ ((4811218253340714821 - 1) / 1001401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 4811218253340714821) ^ ((4811218253340714821 - 1) / 21838578031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4811218253340714821 (3 : ZMod 4811218253340714821)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (11, 1), (1001401, 1), (21838578031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (11, 1), (1001401, 1), (21838578031, 1)] : List FactorBlock).map factorBlockValue).prod = 4811218253340714821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64OctF_1001401
      · exact prime_free64OctF_21838578031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1139058409 : Nat.Prime 1139058409 := by
  have hfermat : (13 : ZMod 1139058409) ^ (1139058409 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 1139058409) ^ ((1139058409 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 1139058409) ^ ((1139058409 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 1139058409) ^ ((1139058409 - 1) / 2281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 1139058409) ^ ((1139058409 - 1) / 20807) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1139058409 (13 : ZMod 1139058409)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (2281, 1), (20807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (2281, 1), (20807, 1)] : List FactorBlock).map factorBlockValue).prod = 1139058409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_2281
      · exact prime_free64OctF_20807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_8464683510949917373 : Nat.Prime 8464683510949917373 := by
  have hfermat : (2 : ZMod 8464683510949917373) ^ (8464683510949917373 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 56809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 8464683510949917373) ^ ((8464683510949917373 - 1) / 1139058409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8464683510949917373 (2 : ZMod 8464683510949917373)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (991, 1), (56809, 1), (1139058409, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (991, 1), (56809, 1), (1139058409, 1)] : List FactorBlock).map factorBlockValue).prod = 8464683510949917373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_991
      · exact prime_free64OctF_56809
      · exact prime_free64OctF_1139058409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_28785499 : Nat.Prime 28785499 := by
  have hfermat : (2 : ZMod 28785499) ^ (28785499 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 28785499) ^ ((28785499 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 28785499) ^ ((28785499 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 28785499) ^ ((28785499 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 28785499) ^ ((28785499 - 1) / 685369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28785499 (2 : ZMod 28785499)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (685369, 1)] : List FactorBlock).map factorBlockValue).prod = 28785499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64OctF_685369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_10496781784408483841 : Nat.Prime 10496781784408483841 := by
  have hfermat : (3 : ZMod 10496781784408483841) ^ (10496781784408483841 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10496781784408483841) ^ ((10496781784408483841 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10496781784408483841) ^ ((10496781784408483841 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10496781784408483841) ^ ((10496781784408483841 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10496781784408483841) ^ ((10496781784408483841 - 1) / 671903) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 10496781784408483841) ^ ((10496781784408483841 - 1) / 28785499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10496781784408483841 (3 : ZMod 10496781784408483841)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 11), (5, 1), (53, 1), (671903, 1), (28785499, 1)] : List FactorBlock).map factorBlockValue).prod = 10496781784408483841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_free64OctF_671903
      · exact prime_free64OctF_28785499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_7062967943 : Nat.Prime 7062967943 := by
  have hfermat : (5 : ZMod 7062967943) ^ (7062967943 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 7062967943) ^ ((7062967943 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 7062967943) ^ ((7062967943 - 1) / 5479) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 7062967943) ^ ((7062967943 - 1) / 644549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7062967943 (5 : ZMod 7062967943)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5479, 1), (644549, 1)] : List FactorBlock).map factorBlockValue).prod = 7062967943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_5479
      · exact prime_free64OctF_644549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_9691183070205617 : Nat.Prime 9691183070205617 := by
  have hfermat : (3 : ZMod 9691183070205617) ^ (9691183070205617 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 9691183070205617) ^ ((9691183070205617 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 9691183070205617) ^ ((9691183070205617 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 9691183070205617) ^ ((9691183070205617 - 1) / 12251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 9691183070205617) ^ ((9691183070205617 - 1) / 7062967943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9691183070205617 (3 : ZMod 9691183070205617)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (12251, 1), (7062967943, 1)] : List FactorBlock).map factorBlockValue).prod = 9691183070205617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64OctF_12251
      · exact prime_free64OctF_7062967943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_13451362101445396397 : Nat.Prime 13451362101445396397 := by
  have hfermat : (2 : ZMod 13451362101445396397) ^ (13451362101445396397 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 13451362101445396397) ^ ((13451362101445396397 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 13451362101445396397) ^ ((13451362101445396397 - 1) / 347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 13451362101445396397) ^ ((13451362101445396397 - 1) / 9691183070205617) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13451362101445396397 (2 : ZMod 13451362101445396397)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (347, 1), (9691183070205617, 1)] : List FactorBlock).map factorBlockValue).prod = 13451362101445396397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_347
      · exact prime_free64OctF_9691183070205617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1295475289 : Nat.Prime 1295475289 := by
  have hfermat : (7 : ZMod 1295475289) ^ (1295475289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 1295475289) ^ ((1295475289 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1295475289 (7 : ZMod 1295475289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (47, 1), (83, 1), (101, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (47, 1), (83, 1), (101, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod = 1295475289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_t64_83
      · exact prime_t64_101
      · exact prime_t64_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_17672454355456607929 : Nat.Prime 17672454355456607929 := by
  have hfermat : (7 : ZMod 17672454355456607929) ^ (17672454355456607929 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 709) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (7 : ZMod 17672454355456607929) ^ ((17672454355456607929 - 1) / 1295475289) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17672454355456607929 (7 : ZMod 17672454355456607929)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (13, 1), (83, 1), (709, 1), (743, 1), (1295475289, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (13, 1), (83, 1), (709, 1), (743, 1), (1295475289, 1)] : List FactorBlock).map factorBlockValue).prod = 17672454355456607929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_83
      · exact prime_free64OctF_709
      · exact prime_free64OctF_743
      · exact prime_free64OctF_1295475289
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

private theorem prime_free64OctF_12583841 : Nat.Prime 12583841 := by
  have hfermat : (3 : ZMod 12583841) ^ (12583841 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 12583841) ^ ((12583841 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 12583841) ^ ((12583841 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 12583841) ^ ((12583841 - 1) / 78649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12583841 (3 : ZMod 12583841)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5, 1), (78649, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5, 1), (78649, 1)] : List FactorBlock).map factorBlockValue).prod = 12583841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_78649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_25167683 : Nat.Prime 25167683 := by
  have hfermat : (2 : ZMod 25167683) ^ (25167683 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 25167683) ^ ((25167683 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 25167683) ^ ((25167683 - 1) / 12583841) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25167683 (2 : ZMod 25167683)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (12583841, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (12583841, 1)] : List FactorBlock).map factorBlockValue).prod = 25167683 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_12583841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_654359759 : Nat.Prime 654359759 := by
  have hfermat : (7 : ZMod 654359759) ^ (654359759 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 654359759) ^ ((654359759 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 654359759) ^ ((654359759 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 654359759) ^ ((654359759 - 1) / 25167683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 654359759 (7 : ZMod 654359759)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (25167683, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (25167683, 1)] : List FactorBlock).map factorBlockValue).prod = 654359759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64OctF_25167683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_20977140676648304671 : Nat.Prime 20977140676648304671 := by
  have hfermat : (12 : ZMod 20977140676648304671) ^ (20977140676648304671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 757) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 1411603) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (12 : ZMod 20977140676648304671) ^ ((20977140676648304671 - 1) / 654359759) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20977140676648304671 (12 : ZMod 20977140676648304671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (757, 1), (1411603, 1), (654359759, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (757, 1), (1411603, 1), (654359759, 1)] : List FactorBlock).map factorBlockValue).prod = 20977140676648304671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_757
      · exact prime_free64OctF_1411603
      · exact prime_free64OctF_654359759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_231454207 : Nat.Prime 231454207 := by
  have hfermat : (5 : ZMod 231454207) ^ (231454207 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 231454207) ^ ((231454207 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 231454207) ^ ((231454207 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 231454207) ^ ((231454207 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 231454207) ^ ((231454207 - 1) / 32719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 231454207 (5 : ZMod 231454207)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (131, 1), (32719, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (131, 1), (32719, 1)] : List FactorBlock).map factorBlockValue).prod = 231454207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_131
      · exact prime_free64OctF_32719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_1388725243 : Nat.Prime 1388725243 := by
  have hfermat : (2 : ZMod 1388725243) ^ (1388725243 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1388725243) ^ ((1388725243 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1388725243) ^ ((1388725243 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1388725243) ^ ((1388725243 - 1) / 231454207) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1388725243 (2 : ZMod 1388725243)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (231454207, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (231454207, 1)] : List FactorBlock).map factorBlockValue).prod = 1388725243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_231454207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_5554900973 : Nat.Prime 5554900973 := by
  have hfermat : (2 : ZMod 5554900973) ^ (5554900973 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5554900973) ^ ((5554900973 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5554900973) ^ ((5554900973 - 1) / 1388725243) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5554900973 (2 : ZMod 5554900973)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1388725243, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1388725243, 1)] : List FactorBlock).map factorBlockValue).prod = 5554900973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_1388725243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_11109801947 : Nat.Prime 11109801947 := by
  have hfermat : (2 : ZMod 11109801947) ^ (11109801947 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 11109801947) ^ ((11109801947 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 11109801947) ^ ((11109801947 - 1) / 5554900973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11109801947 (2 : ZMod 11109801947)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5554900973, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5554900973, 1)] : List FactorBlock).map factorBlockValue).prod = 11109801947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_5554900973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_169180064048917 : Nat.Prime 169180064048917 := by
  have hfermat : (2 : ZMod 169180064048917) ^ (169180064048917 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 169180064048917) ^ ((169180064048917 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 169180064048917) ^ ((169180064048917 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 169180064048917) ^ ((169180064048917 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 169180064048917) ^ ((169180064048917 - 1) / 11109801947) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 169180064048917 (2 : ZMod 169180064048917)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (47, 1), (11109801947, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (47, 1), (11109801947, 1)] : List FactorBlock).map factorBlockValue).prod = 169180064048917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_free64OctF_11109801947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_105511515465003771889 : Nat.Prime 105511515465003771889 := by
  have hfermat : (14 : ZMod 105511515465003771889) ^ (105511515465003771889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 105511515465003771889) ^ ((105511515465003771889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 105511515465003771889) ^ ((105511515465003771889 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 105511515465003771889) ^ ((105511515465003771889 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 105511515465003771889) ^ ((105511515465003771889 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 105511515465003771889) ^ ((105511515465003771889 - 1) / 169180064048917) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 105511515465003771889 (14 : ZMod 105511515465003771889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (71, 1), (169180064048917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (71, 1), (169180064048917, 1)] : List FactorBlock).map factorBlockValue).prod = 105511515465003771889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_t64_71
      · exact prime_free64OctF_169180064048917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_20543417 : Nat.Prime 20543417 := by
  have hfermat : (3 : ZMod 20543417) ^ (20543417 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 20543417) ^ ((20543417 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 20543417) ^ ((20543417 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 20543417) ^ ((20543417 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 20543417) ^ ((20543417 - 1) / 359) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20543417 (3 : ZMod 20543417)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (23, 1), (311, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (23, 1), (311, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod = 20543417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_t64_311
      · exact prime_free64OctF_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_154880888359567 : Nat.Prime 154880888359567 := by
  have hfermat : (3 : ZMod 154880888359567) ^ (154880888359567 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 154880888359567) ^ ((154880888359567 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 154880888359567) ^ ((154880888359567 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 154880888359567) ^ ((154880888359567 - 1) / 1256533) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 154880888359567) ^ ((154880888359567 - 1) / 20543417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 154880888359567 (3 : ZMod 154880888359567)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1256533, 1), (20543417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1256533, 1), (20543417, 1)] : List FactorBlock).map factorBlockValue).prod = 154880888359567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_1256533
      · exact prime_free64OctF_20543417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_421554182413516022333 : Nat.Prime 421554182413516022333 := by
  have hfermat : (2 : ZMod 421554182413516022333) ^ (421554182413516022333 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 421554182413516022333) ^ ((421554182413516022333 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 421554182413516022333) ^ ((421554182413516022333 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 421554182413516022333) ^ ((421554182413516022333 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 421554182413516022333) ^ ((421554182413516022333 - 1) / 8837) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 421554182413516022333) ^ ((421554182413516022333 - 1) / 154880888359567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 421554182413516022333 (2 : ZMod 421554182413516022333)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 1), (8837, 1), (154880888359567, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 1), (8837, 1), (154880888359567, 1)] : List FactorBlock).map factorBlockValue).prod = 421554182413516022333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64OctF_8837
      · exact prime_free64OctF_154880888359567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_28954561 : Nat.Prime 28954561 := by
  have hfermat : (14 : ZMod 28954561) ^ (28954561 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 28954561) ^ ((28954561 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 28954561) ^ ((28954561 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 28954561) ^ ((28954561 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 28954561) ^ ((28954561 - 1) / 30161) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28954561 (14 : ZMod 28954561)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (5, 1), (30161, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (5, 1), (30161, 1)] : List FactorBlock).map factorBlockValue).prod = 28954561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_30161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_42831646053305687 : Nat.Prime 42831646053305687 := by
  have hfermat : (5 : ZMod 42831646053305687) ^ (42831646053305687 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 42831646053305687) ^ ((42831646053305687 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 42831646053305687) ^ ((42831646053305687 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 42831646053305687) ^ ((42831646053305687 - 1) / 5646073) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 42831646053305687) ^ ((42831646053305687 - 1) / 28954561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 42831646053305687 (5 : ZMod 42831646053305687)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (131, 1), (5646073, 1), (28954561, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (131, 1), (5646073, 1), (28954561, 1)] : List FactorBlock).map factorBlockValue).prod = 42831646053305687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_131
      · exact prime_free64OctF_5646073
      · exact prime_free64OctF_28954561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_885158797337615327543 : Nat.Prime 885158797337615327543 := by
  have hfermat : (5 : ZMod 885158797337615327543) ^ (885158797337615327543 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 885158797337615327543) ^ ((885158797337615327543 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 885158797337615327543) ^ ((885158797337615327543 - 1) / 10333) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 885158797337615327543) ^ ((885158797337615327543 - 1) / 42831646053305687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 885158797337615327543 (5 : ZMod 885158797337615327543)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (10333, 1), (42831646053305687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (10333, 1), (42831646053305687, 1)] : List FactorBlock).map factorBlockValue).prod = 885158797337615327543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_10333
      · exact prime_free64OctF_42831646053305687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_112799441 : Nat.Prime 112799441 := by
  have hfermat : (3 : ZMod 112799441) ^ (112799441 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 112799441) ^ ((112799441 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 112799441) ^ ((112799441 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 112799441) ^ ((112799441 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 112799441) ^ ((112799441 - 1) / 108461) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 112799441 (3 : ZMod 112799441)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (13, 1), (108461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (13, 1), (108461, 1)] : List FactorBlock).map factorBlockValue).prod = 112799441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64OctF_108461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_31823669 : Nat.Prime 31823669 := by
  have hfermat : (2 : ZMod 31823669) ^ (31823669 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 31823669) ^ ((31823669 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 31823669) ^ ((31823669 - 1) / 7955917) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 31823669 (2 : ZMod 31823669)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7955917, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7955917, 1)] : List FactorBlock).map factorBlockValue).prod = 31823669 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_7955917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64OctF_2673188197 : Nat.Prime 2673188197 := by
  have hfermat : (2 : ZMod 2673188197) ^ (2673188197 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2673188197) ^ ((2673188197 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2673188197) ^ ((2673188197 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2673188197) ^ ((2673188197 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2673188197) ^ ((2673188197 - 1) / 31823669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2673188197 (2 : ZMod 2673188197)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (31823669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (31823669, 1)] : List FactorBlock).map factorBlockValue).prod = 2673188197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64OctF_31823669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_106927527881 : Nat.Prime 106927527881 := by
  have hfermat : (3 : ZMod 106927527881) ^ (106927527881 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 106927527881) ^ ((106927527881 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 106927527881) ^ ((106927527881 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 106927527881) ^ ((106927527881 - 1) / 2673188197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 106927527881 (3 : ZMod 106927527881)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (2673188197, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (2673188197, 1)] : List FactorBlock).map factorBlockValue).prod = 106927527881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_2673188197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_1278504729483803739227 : Nat.Prime 1278504729483803739227 := by
  have hfermat : (2 : ZMod 1278504729483803739227) ^ (1278504729483803739227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1278504729483803739227) ^ ((1278504729483803739227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1278504729483803739227) ^ ((1278504729483803739227 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1278504729483803739227) ^ ((1278504729483803739227 - 1) / 112799441) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1278504729483803739227) ^ ((1278504729483803739227 - 1) / 106927527881) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1278504729483803739227 (2 : ZMod 1278504729483803739227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (53, 1), (112799441, 1), (106927527881, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (53, 1), (112799441, 1), (106927527881, 1)] : List FactorBlock).map factorBlockValue).prod = 1278504729483803739227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_free64OctF_112799441
      · exact prime_free64OctF_106927527881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_402625124287 : Nat.Prime 402625124287 := by
  have hfermat : (6 : ZMod 402625124287) ^ (402625124287 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 8761) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 402625124287) ^ ((402625124287 - 1) / 9043) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 402625124287 (6 : ZMod 402625124287)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (11, 2), (8761, 1), (9043, 1)] : List FactorBlock).map factorBlockValue).prod = 402625124287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64OctF_8761
      · exact prime_free64OctF_9043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_9663002982889 : Nat.Prime 9663002982889 := by
  have hfermat : (41 : ZMod 9663002982889) ^ (9663002982889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (41 : ZMod 9663002982889) ^ ((9663002982889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (41 : ZMod 9663002982889) ^ ((9663002982889 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (41 : ZMod 9663002982889) ^ ((9663002982889 - 1) / 402625124287) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9663002982889 (41 : ZMod 9663002982889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (402625124287, 1)] : List FactorBlock).map factorBlockValue).prod = 9663002982889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_402625124287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_212586065623559 : Nat.Prime 212586065623559 := by
  have hfermat : (11 : ZMod 212586065623559) ^ (212586065623559 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 212586065623559) ^ ((212586065623559 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 212586065623559) ^ ((212586065623559 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 212586065623559) ^ ((212586065623559 - 1) / 9663002982889) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 212586065623559 (11 : ZMod 212586065623559)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (9663002982889, 1)] : List FactorBlock).map factorBlockValue).prod = 212586065623559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64OctF_9663002982889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_5893954621823010734653 : Nat.Prime 5893954621823010734653 := by
  have hfermat : (5 : ZMod 5893954621823010734653) ^ (5893954621823010734653 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (5 : ZMod 5893954621823010734653) ^ ((5893954621823010734653 - 1) / 212586065623559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5893954621823010734653 (5 : ZMod 5893954621823010734653)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (311, 1), (212586065623559, 1)] : List FactorBlock).map factorBlockValue).prod = 5893954621823010734653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_t64_311
      · exact prime_free64OctF_212586065623559
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

private theorem prime_free64OctF_73650013801457 : Nat.Prime 73650013801457 := by
  have hfermat : (3 : ZMod 73650013801457) ^ (73650013801457 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 73650013801457) ^ ((73650013801457 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 73650013801457) ^ ((73650013801457 - 1) / 1627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 73650013801457) ^ ((73650013801457 - 1) / 5987) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 73650013801457) ^ ((73650013801457 - 1) / 472559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 73650013801457 (3 : ZMod 73650013801457)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (1627, 1), (5987, 1), (472559, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (1627, 1), (5987, 1), (472559, 1)] : List FactorBlock).map factorBlockValue).prod = 73650013801457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_1627
      · exact prime_free64OctF_5987
      · exact prime_free64OctF_472559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_16502686268178916959227 : Nat.Prime 16502686268178916959227 := by
  have hfermat : (2 : ZMod 16502686268178916959227) ^ (16502686268178916959227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 16502686268178916959227) ^ ((16502686268178916959227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 16502686268178916959227) ^ ((16502686268178916959227 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 16502686268178916959227) ^ ((16502686268178916959227 - 1) / 2732549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 16502686268178916959227) ^ ((16502686268178916959227 - 1) / 73650013801457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16502686268178916959227 (2 : ZMod 16502686268178916959227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41, 1), (2732549, 1), (73650013801457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41, 1), (2732549, 1), (73650013801457, 1)] : List FactorBlock).map factorBlockValue).prod = 16502686268178916959227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_free64OctF_2732549
      · exact prime_free64OctF_73650013801457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_244140209 : Nat.Prime 244140209 := by
  have hfermat : (3 : ZMod 244140209) ^ (244140209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 244140209) ^ ((244140209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 244140209) ^ ((244140209 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 244140209) ^ ((244140209 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 244140209) ^ ((244140209 - 1) / 31723) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 244140209 (3 : ZMod 244140209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (13, 1), (37, 1), (31723, 1)] : List FactorBlock).map factorBlockValue).prod = 244140209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_37
      · exact prime_free64OctF_31723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_5381573389 : Nat.Prime 5381573389 := by
  have hfermat : (2 : ZMod 5381573389) ^ (5381573389 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5381573389) ^ ((5381573389 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5381573389) ^ ((5381573389 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5381573389) ^ ((5381573389 - 1) / 2837) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5381573389) ^ ((5381573389 - 1) / 158077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5381573389 (2 : ZMod 5381573389)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2837, 1), (158077, 1)] : List FactorBlock).map factorBlockValue).prod = 5381573389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_2837
      · exact prime_free64OctF_158077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_34890825049700005681357 : Nat.Prime 34890825049700005681357 := by
  have hfermat : (2 : ZMod 34890825049700005681357) ^ (34890825049700005681357 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 34890825049700005681357) ^ ((34890825049700005681357 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 34890825049700005681357) ^ ((34890825049700005681357 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 34890825049700005681357) ^ ((34890825049700005681357 - 1) / 2213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 34890825049700005681357) ^ ((34890825049700005681357 - 1) / 244140209) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 34890825049700005681357) ^ ((34890825049700005681357 - 1) / 5381573389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 34890825049700005681357 (2 : ZMod 34890825049700005681357)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2213, 1), (244140209, 1), (5381573389, 1)] : List FactorBlock).map factorBlockValue).prod = 34890825049700005681357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_2213
      · exact prime_free64OctF_244140209
      · exact prime_free64OctF_5381573389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_36407143 : Nat.Prime 36407143 := by
  have hfermat : (6 : ZMod 36407143) ^ (36407143 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 36407143) ^ ((36407143 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 36407143) ^ ((36407143 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 36407143) ^ ((36407143 - 1) / 2022619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 36407143 (6 : ZMod 36407143)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (2022619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (2022619, 1)] : List FactorBlock).map factorBlockValue).prod = 36407143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_2022619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_42355637 : Nat.Prime 42355637 := by
  have hfermat : (2 : ZMod 42355637) ^ (42355637 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 42355637) ^ ((42355637 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 42355637) ^ ((42355637 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 42355637) ^ ((42355637 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 42355637) ^ ((42355637 - 1) / 32783) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 42355637 (2 : ZMod 42355637)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (17, 1), (19, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (17, 1), (19, 1), (32783, 1)] : List FactorBlock).map factorBlockValue).prod = 42355637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_t64_19
      · exact prime_free64OctF_32783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_544862914369 : Nat.Prime 544862914369 := by
  have hfermat : (13 : ZMod 544862914369) ^ (544862914369 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 544862914369) ^ ((544862914369 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 544862914369) ^ ((544862914369 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 544862914369) ^ ((544862914369 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 544862914369) ^ ((544862914369 - 1) / 42355637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 544862914369 (13 : ZMod 544862914369)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (67, 1), (42355637, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (67, 1), (42355637, 1)] : List FactorBlock).map factorBlockValue).prod = 544862914369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_free64OctF_42355637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_69349809527745966433433 : Nat.Prime 69349809527745966433433 := by
  have hfermat : (3 : ZMod 69349809527745966433433) ^ (69349809527745966433433 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 69349809527745966433433) ^ ((69349809527745966433433 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 69349809527745966433433) ^ ((69349809527745966433433 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 69349809527745966433433) ^ ((69349809527745966433433 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 69349809527745966433433) ^ ((69349809527745966433433 - 1) / 36407143) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 69349809527745966433433) ^ ((69349809527745966433433 - 1) / 544862914369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 69349809527745966433433 (3 : ZMod 69349809527745966433433)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (23, 1), (36407143, 1), (544862914369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (23, 1), (36407143, 1), (544862914369, 1)] : List FactorBlock).map factorBlockValue).prod = 69349809527745966433433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_23
      · exact prime_free64OctF_36407143
      · exact prime_free64OctF_544862914369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1440461809 : Nat.Prime 1440461809 := by
  have hfermat : (7 : ZMod 1440461809) ^ (1440461809 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 1440461809) ^ ((1440461809 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 1440461809) ^ ((1440461809 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 1440461809) ^ ((1440461809 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 1440461809) ^ ((1440461809 - 1) / 163987) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1440461809 (7 : ZMod 1440461809)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (61, 1), (163987, 1)] : List FactorBlock).map factorBlockValue).prod = 1440461809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_61
      · exact prime_free64OctF_163987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_621509730110564998034623 : Nat.Prime 621509730110564998034623 := by
  have hfermat : (5 : ZMod 621509730110564998034623) ^ (621509730110564998034623 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 3061) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 61379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 382747) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 621509730110564998034623) ^ ((621509730110564998034623 - 1) / 1440461809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 621509730110564998034623 (5 : ZMod 621509730110564998034623)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3061, 1), (61379, 1), (382747, 1), (1440461809, 1)] : List FactorBlock).map factorBlockValue).prod = 621509730110564998034623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_3061
      · exact prime_free64OctF_61379
      · exact prime_free64OctF_382747
      · exact prime_free64OctF_1440461809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_1255074433 : Nat.Prime 1255074433 := by
  have hfermat : (10 : ZMod 1255074433) ^ (1255074433 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 1255074433) ^ ((1255074433 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 1255074433) ^ ((1255074433 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 1255074433) ^ ((1255074433 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 1255074433) ^ ((1255074433 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 1255074433) ^ ((1255074433 - 1) / 1787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1255074433 (10 : ZMod 1255074433)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 7), (3, 1), (31, 1), (59, 1), (1787, 1)] : List FactorBlock).map factorBlockValue).prod = 1255074433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_59
      · exact prime_free64OctF_1787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_17483007257 : Nat.Prime 17483007257 := by
  have hfermat : (6 : ZMod 17483007257) ^ (17483007257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 17483007257) ^ ((17483007257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 17483007257) ^ ((17483007257 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 17483007257) ^ ((17483007257 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 17483007257) ^ ((17483007257 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 17483007257) ^ ((17483007257 - 1) / 492979) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17483007257 (6 : ZMod 17483007257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (13, 1), (31, 1), (492979, 1)] : List FactorBlock).map factorBlockValue).prod = 17483007257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_free64OctF_492979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1449300501505145286560051 : Nat.Prime 1449300501505145286560051 := by
  have hfermat : (6 : ZMod 1449300501505145286560051) ^ (1449300501505145286560051 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1449300501505145286560051) ^ ((1449300501505145286560051 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1449300501505145286560051) ^ ((1449300501505145286560051 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1449300501505145286560051) ^ ((1449300501505145286560051 - 1) / 1321) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1449300501505145286560051) ^ ((1449300501505145286560051 - 1) / 1255074433) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1449300501505145286560051) ^ ((1449300501505145286560051 - 1) / 17483007257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1449300501505145286560051 (6 : ZMod 1449300501505145286560051)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (1321, 1), (1255074433, 1), (17483007257, 1)] : List FactorBlock).map factorBlockValue).prod = 1449300501505145286560051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_1321
      · exact prime_free64OctF_1255074433
      · exact prime_free64OctF_17483007257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_77954273 : Nat.Prime 77954273 := by
  have hfermat : (3 : ZMod 77954273) ^ (77954273 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 77954273) ^ ((77954273 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 77954273) ^ ((77954273 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 77954273) ^ ((77954273 - 1) / 221461) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 77954273 (3 : ZMod 77954273)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11, 1), (221461, 1)] : List FactorBlock).map factorBlockValue).prod = 77954273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64OctF_221461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_935451277 : Nat.Prime 935451277 := by
  have hfermat : (5 : ZMod 935451277) ^ (935451277 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 935451277) ^ ((935451277 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 935451277) ^ ((935451277 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 935451277) ^ ((935451277 - 1) / 77954273) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 935451277 (5 : ZMod 935451277)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (77954273, 1)] : List FactorBlock).map factorBlockValue).prod = 935451277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_77954273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_2129669261 : Nat.Prime 2129669261 := by
  have hfermat : (2 : ZMod 2129669261) ^ (2129669261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2129669261) ^ ((2129669261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2129669261) ^ ((2129669261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2129669261) ^ ((2129669261 - 1) / 887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2129669261) ^ ((2129669261 - 1) / 120049) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2129669261 (2 : ZMod 2129669261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (887, 1), (120049, 1)] : List FactorBlock).map factorBlockValue).prod = 2129669261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_887
      · exact prime_free64OctF_120049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_2321014741796951690819851 : Nat.Prime 2321014741796951690819851 := by
  have hfermat : (10 : ZMod 2321014741796951690819851) ^ (2321014741796951690819851 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 863) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 935451277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (10 : ZMod 2321014741796951690819851) ^ ((2321014741796951690819851 - 1) / 2129669261) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2321014741796951690819851 (10 : ZMod 2321014741796951690819851)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (863, 1), (935451277, 1), (2129669261, 1)] : List FactorBlock).map factorBlockValue).prod = 2321014741796951690819851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_863
      · exact prime_free64OctF_935451277
      · exact prime_free64OctF_2129669261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_224359867 : Nat.Prime 224359867 := by
  have hfermat : (2 : ZMod 224359867) ^ (224359867 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 224359867) ^ ((224359867 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 224359867) ^ ((224359867 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 224359867) ^ ((224359867 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 224359867) ^ ((224359867 - 1) / 656023) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 224359867 (2 : ZMod 224359867)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (19, 1), (656023, 1)] : List FactorBlock).map factorBlockValue).prod = 224359867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_free64OctF_656023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_15857351 : Nat.Prime 15857351 := by
  have hfermat : (17 : ZMod 15857351) ^ (15857351 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 15857351) ^ ((15857351 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 15857351) ^ ((15857351 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 15857351) ^ ((15857351 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 15857351) ^ ((15857351 - 1) / 13789) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15857351 (17 : ZMod 15857351)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (23, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (23, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod = 15857351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_free64OctF_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_98372345516581 : Nat.Prime 98372345516581 := by
  have hfermat : (2 : ZMod 98372345516581) ^ (98372345516581 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 98372345516581) ^ ((98372345516581 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 98372345516581) ^ ((98372345516581 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 98372345516581) ^ ((98372345516581 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 98372345516581) ^ ((98372345516581 - 1) / 103393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 98372345516581) ^ ((98372345516581 - 1) / 15857351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 98372345516581 (2 : ZMod 98372345516581)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (103393, 1), (15857351, 1)] : List FactorBlock).map factorBlockValue).prod = 98372345516581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64OctF_103393
      · exact prime_free64OctF_15857351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_3001629664494629685842873 : Nat.Prime 3001629664494629685842873 := by
  have hfermat : (3 : ZMod 3001629664494629685842873) ^ (3001629664494629685842873 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3001629664494629685842873) ^ ((3001629664494629685842873 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3001629664494629685842873) ^ ((3001629664494629685842873 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3001629664494629685842873) ^ ((3001629664494629685842873 - 1) / 224359867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3001629664494629685842873) ^ ((3001629664494629685842873 - 1) / 98372345516581) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3001629664494629685842873 (3 : ZMod 3001629664494629685842873)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (17, 1), (224359867, 1), (98372345516581, 1)] : List FactorBlock).map factorBlockValue).prod = 3001629664494629685842873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64OctF_224359867
      · exact prime_free64OctF_98372345516581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_506288942577679 : Nat.Prime 506288942577679 := by
  have hfermat : (3 : ZMod 506288942577679) ^ (506288942577679 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 197) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 5827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 506288942577679) ^ ((506288942577679 - 1) / 5654479) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 506288942577679 (3 : ZMod 506288942577679)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (197, 1), (5827, 1), (5654479, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (197, 1), (5827, 1), (5654479, 1)] : List FactorBlock).map factorBlockValue).prod = 506288942577679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_197
      · exact prime_free64OctF_5827
      · exact prime_free64OctF_5654479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_6627985334844133244632721 : Nat.Prime 6627985334844133244632721 := by
  have hfermat : (3 : ZMod 6627985334844133244632721) ^ (6627985334844133244632721 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 6627985334844133244632721) ^ ((6627985334844133244632721 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 6627985334844133244632721) ^ ((6627985334844133244632721 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 6627985334844133244632721) ^ ((6627985334844133244632721 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 6627985334844133244632721) ^ ((6627985334844133244632721 - 1) / 9625963) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 6627985334844133244632721) ^ ((6627985334844133244632721 - 1) / 506288942577679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6627985334844133244632721 (3 : ZMod 6627985334844133244632721)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (17, 1), (9625963, 1), (506288942577679, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (17, 1), (9625963, 1), (506288942577679, 1)] : List FactorBlock).map factorBlockValue).prod = 6627985334844133244632721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_free64OctF_9625963
      · exact prime_free64OctF_506288942577679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_1779319879 : Nat.Prime 1779319879 := by
  have hfermat : (6 : ZMod 1779319879) ^ (1779319879 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 1779319879) ^ ((1779319879 - 1) / 1051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1779319879 (6 : ZMod 1779319879)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (173, 1), (233, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (173, 1), (233, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod = 1779319879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64OctF_173
      · exact prime_t64_233
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

private theorem prime_free64OctF_10857409901659 : Nat.Prime 10857409901659 := by
  have hfermat : (3 : ZMod 10857409901659) ^ (10857409901659 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10857409901659) ^ ((10857409901659 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10857409901659) ^ ((10857409901659 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10857409901659) ^ ((10857409901659 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 10857409901659) ^ ((10857409901659 - 1) / 1779319879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10857409901659 (3 : ZMod 10857409901659)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (113, 1), (1779319879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (113, 1), (1779319879, 1)] : List FactorBlock).map factorBlockValue).prod = 10857409901659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_113
      · exact prime_free64OctF_1779319879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_9740612845337361627282073 : Nat.Prime 9740612845337361627282073 := by
  have hfermat : (10 : ZMod 9740612845337361627282073) ^ (9740612845337361627282073 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 463) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 2182057) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (10 : ZMod 9740612845337361627282073) ^ ((9740612845337361627282073 - 1) / 10857409901659) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9740612845337361627282073 (10 : ZMod 9740612845337361627282073)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (37, 1), (463, 1), (2182057, 1), (10857409901659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (37, 1), (463, 1), (2182057, 1), (10857409901659, 1)] : List FactorBlock).map factorBlockValue).prod = 9740612845337361627282073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_37
      · exact prime_free64OctF_463
      · exact prime_free64OctF_2182057
      · exact prime_free64OctF_10857409901659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_78588701 : Nat.Prime 78588701 := by
  have hfermat : (2 : ZMod 78588701) ^ (78588701 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 78588701) ^ ((78588701 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 78588701) ^ ((78588701 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 78588701) ^ ((78588701 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 78588701) ^ ((78588701 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 78588701) ^ ((78588701 - 1) / 727) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 78588701 (2 : ZMod 78588701)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (23, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (23, 1), (47, 1), (727, 1)] : List FactorBlock).map factorBlockValue).prod = 78588701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_47
      · exact prime_free64OctF_727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_338915891 : Nat.Prime 338915891 := by
  have hfermat : (2 : ZMod 338915891) ^ (338915891 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 338915891) ^ ((338915891 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 338915891) ^ ((338915891 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 338915891) ^ ((338915891 - 1) / 241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 338915891) ^ ((338915891 - 1) / 140629) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 338915891 (2 : ZMod 338915891)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (241, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (241, 1), (140629, 1)] : List FactorBlock).map factorBlockValue).prod = 338915891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64OctF_241
      · exact prime_free64OctF_140629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_84051140969 : Nat.Prime 84051140969 := by
  have hfermat : (3 : ZMod 84051140969) ^ (84051140969 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 84051140969) ^ ((84051140969 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 84051140969) ^ ((84051140969 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 84051140969) ^ ((84051140969 - 1) / 338915891) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 84051140969 (3 : ZMod 84051140969)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (338915891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (338915891, 1)] : List FactorBlock).map factorBlockValue).prod = 84051140969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64OctF_338915891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_14439900874538287236779989 : Nat.Prime 14439900874538287236779989 := by
  have hfermat : (6 : ZMod 14439900874538287236779989) ^ (14439900874538287236779989 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 16561) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 78588701) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 14439900874538287236779989) ^ ((14439900874538287236779989 - 1) / 84051140969) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14439900874538287236779989 (6 : ZMod 14439900874538287236779989)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (16561, 1), (78588701, 1), (84051140969, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (16561, 1), (78588701, 1), (84051140969, 1)] : List FactorBlock).map factorBlockValue).prod = 14439900874538287236779989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64OctF_16561
      · exact prime_free64OctF_78588701
      · exact prime_free64OctF_84051140969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_818876899 : Nat.Prime 818876899 := by
  have hfermat : (2 : ZMod 818876899) ^ (818876899 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 818876899) ^ ((818876899 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 818876899) ^ ((818876899 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 818876899) ^ ((818876899 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 818876899) ^ ((818876899 - 1) / 389) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 818876899) ^ ((818876899 - 1) / 5569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 818876899 (2 : ZMod 818876899)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (7, 1), (389, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (7, 1), (389, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod = 818876899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64OctF_389
      · exact prime_free64OctF_5569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_16391915204198575632739849 : Nat.Prime 16391915204198575632739849 := by
  have hfermat : (11 : ZMod 16391915204198575632739849) ^ (16391915204198575632739849 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 877) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 5003) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 83047) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (11 : ZMod 16391915204198575632739849) ^ ((16391915204198575632739849 - 1) / 818876899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16391915204198575632739849 (11 : ZMod 16391915204198575632739849)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (7, 1), (109, 1), (877, 1), (5003, 1), (83047, 1), (818876899, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (7, 1), (109, 1), (877, 1), (5003, 1), (83047, 1), (818876899, 1)] : List FactorBlock).map factorBlockValue).prod = 16391915204198575632739849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_109
      · exact prime_free64OctF_877
      · exact prime_free64OctF_5003
      · exact prime_free64OctF_83047
      · exact prime_free64OctF_818876899
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

private theorem prime_free64OctF_234103828649 : Nat.Prime 234103828649 := by
  have hfermat : (3 : ZMod 234103828649) ^ (234103828649 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 234103828649) ^ ((234103828649 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 234103828649) ^ ((234103828649 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 234103828649) ^ ((234103828649 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 234103828649) ^ ((234103828649 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 234103828649) ^ ((234103828649 - 1) / 307381) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 234103828649 (3 : ZMod 234103828649)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (37, 1), (83, 1), (307381, 1)] : List FactorBlock).map factorBlockValue).prod = 234103828649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_37
      · exact prime_t64_83
      · exact prime_free64OctF_307381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64OctF_97678393 : Nat.Prime 97678393 := by
  have hfermat : (11 : ZMod 97678393) ^ (97678393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 97678393) ^ ((97678393 - 1) / 431) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 97678393 (11 : ZMod 97678393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (7, 1), (19, 1), (71, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod = 97678393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_71
      · exact prime_t64_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64OctF_20782640965039 : Nat.Prime 20782640965039 := by
  have hfermat : (3 : ZMod 20782640965039) ^ (20782640965039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 20782640965039) ^ ((20782640965039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 20782640965039) ^ ((20782640965039 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 20782640965039) ^ ((20782640965039 - 1) / 35461) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 20782640965039) ^ ((20782640965039 - 1) / 97678393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20782640965039 (3 : ZMod 20782640965039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (35461, 1), (97678393, 1)] : List FactorBlock).map factorBlockValue).prod = 20782640965039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64OctF_35461
      · exact prime_free64OctF_97678393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64OctF_38922366554825424444818489 : Nat.Prime 38922366554825424444818489 := by
  have hfermat : (3 : ZMod 38922366554825424444818489) ^ (38922366554825424444818489 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 38922366554825424444818489) ^ ((38922366554825424444818489 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 38922366554825424444818489) ^ ((38922366554825424444818489 - 1) / 234103828649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 38922366554825424444818489) ^ ((38922366554825424444818489 - 1) / 20782640965039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 38922366554825424444818489 (3 : ZMod 38922366554825424444818489)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (234103828649, 1), (20782640965039, 1)] : List FactorBlock).map factorBlockValue).prod = 38922366554825424444818489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64OctF_234103828649
      · exact prime_free64OctF_20782640965039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64OctF_121258141959263822308857601 : Nat.Prime 121258141959263822308857601 := by
  have hfermat : (65 : ZMod 121258141959263822308857601) ^ (121258141959263822308857601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (65 : ZMod 121258141959263822308857601) ^ ((121258141959263822308857601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 121258141959263822308857601 (65 : ZMod 121258141959263822308857601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 121258141959263822308857601 - 1 by
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

private theorem prime_free64OctF_137074421345254755653491201 : Nat.Prime 137074421345254755653491201 := by
  have hfermat : (23 : ZMod 137074421345254755653491201) ^ (137074421345254755653491201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (23 : ZMod 137074421345254755653491201) ^ ((137074421345254755653491201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 137074421345254755653491201 (23 : ZMod 137074421345254755653491201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 137074421345254755653491201 - 1 by
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

private theorem prime_free64OctF_152550565690686744195014401 : Nat.Prime 152550565690686744195014401 := by
  have hfermat : (113 : ZMod 152550565690686744195014401) ^ (152550565690686744195014401 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (113 : ZMod 152550565690686744195014401) ^ ((152550565690686744195014401 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 152550565690686744195014401 (113 : ZMod 152550565690686744195014401)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 152550565690686744195014401 - 1 by
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

private theorem prime_free64OctF_171966092233137784365288961 : Nat.Prime 171966092233137784365288961 := by
  have hfermat : (73 : ZMod 171966092233137784365288961) ^ (171966092233137784365288961 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (73 : ZMod 171966092233137784365288961) ^ ((171966092233137784365288961 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 171966092233137784365288961 (73 : ZMod 171966092233137784365288961)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 3), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 3), (5, 1), (7, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 171966092233137784365288961 - 1 by
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

private theorem prime_free64OctF_450387384420122768575756801 : Nat.Prime 450387384420122768575756801 := by
  have hfermat : (101 : ZMod 450387384420122768575756801) ^ (450387384420122768575756801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (101 : ZMod 450387384420122768575756801) ^ ((450387384420122768575756801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 450387384420122768575756801 (101 : ZMod 450387384420122768575756801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 9), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 450387384420122768575756801 - 1 by
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

private theorem prime_free64OctF_525451948490143230005049601 : Nat.Prime 525451948490143230005049601 := by
  have hfermat : (179 : ZMod 525451948490143230005049601) ^ (525451948490143230005049601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (179 : ZMod 525451948490143230005049601) ^ ((525451948490143230005049601 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 525451948490143230005049601 (179 : ZMod 525451948490143230005049601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 525451948490143230005049601 - 1 by
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

private theorem prime_free64OctF_1576355845470429690015148801 : Nat.Prime 1576355845470429690015148801 := by
  have hfermat : (101 : ZMod 1576355845470429690015148801) ^ (1576355845470429690015148801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (101 : ZMod 1576355845470429690015148801) ^ ((1576355845470429690015148801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1576355845470429690015148801 (101 : ZMod 1576355845470429690015148801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 8), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 1576355845470429690015148801 - 1 by
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

private theorem phi_free64OctF_9458135072822578140090892791 :
    Nat.totient 9458135072822578140090892791 = 6305415730216807473072663552 := by
  rw [← show
    ((([(3, 2), (824099, 1), (25940193589, 1), (49159833409, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892791 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64OctF_824099, prime_free64OctF_25940193589, prime_free64OctF_49159833409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892792 :
    Nat.totient 9458135072822578140090892792 = 4691828835391259107078235136 := by
  rw [← show
    ((([(2, 3), (127, 1), (4597709, 1), (5054317, 1), (400597142329, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892792 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64OctF_127, prime_free64OctF_4597709, prime_free64OctF_5054317, prime_free64OctF_400597142329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892793 :
    Nat.totient 9458135072822578140090892793 = 8015872260266065037447827200 := by
  rw [← show
    ((([(7, 1), (89, 1), (723721, 1), (20977140676648304671, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892793 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_89, prime_free64OctF_723721, prime_free64OctF_20977140676648304671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892794 :
    Nat.totient 9458135072822578140090892794 = 3133825907520671847475622400 := by
  rw [← show
    ((([(2, 1), (3, 1), (167, 1), (443941, 1), (14839757, 1), (1432800567881, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892794 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_167, prime_free64OctF_443941, prime_free64OctF_14839757, prime_free64OctF_1432800567881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892795 :
    Nat.totient 9458135072822578140090892795 = 7508748454759909363125593760 := by
  rw [← show
    ((([(5, 1), (131, 1), (14439900874538287236779989, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892795 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64OctF_131, prime_free64OctF_14439900874538287236779989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892796 :
    Nat.totient 9458135072822578140090892796 = 4725418243661272074321048960 := by
  rw [← show
    ((([(2, 2), (1531, 1), (11923, 1), (28807, 1), (4496625855541289, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892796 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64OctF_1531, prime_free64OctF_11923, prime_free64OctF_28807, prime_free64OctF_4496625855541289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892797 :
    Nat.totient 9458135072822578140090892797 = 6305423364952351737415850928 := by
  rw [← show
    ((([(3, 1), (372454763, 1), (8464683510949917373, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892797 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64OctF_372454763, prime_free64OctF_8464683510949917373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892798 :
    Nat.totient 9458135072822578140090892798 = 4728768843324818344589293056 := by
  rw [← show
    ((([(2, 1), (18713, 1), (109469, 1), (1701179, 1), (1357034643673, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892798 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64OctF_18713, prime_free64OctF_109469, prime_free64OctF_1701179, prime_free64OctF_1357034643673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892799 :
    Nat.totient 9458135072822578140090892799 = 9458116623046003550467714560 := by
  rw [← show
    ((([(566437, 1), (5397907, 1), (3093346001652161, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892799 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64OctF_566437, prime_free64OctF_5397907, prime_free64OctF_3093346001652161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892800 :
    Nat.totient 9458135072822578140090892800 = 1244570947674885115084800000 := by
  rw [← show
    ((([(2, 9), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892800 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892801 :
    Nat.totient 9458135072822578140090892801 = 9397888661980578118038196608 := by
  rw [← show
    ((([(157, 1), (4315799, 1), (7041049, 1), (1982473007243, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892801 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_157, prime_free64OctF_4315799, prime_free64OctF_7041049, prime_free64OctF_1982473007243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892802 :
    Nat.totient 9458135072822578140090892802 = 4716759632945508174057984000 := by
  rw [← show
    ((([(2, 1), (401, 1), (11069, 1), (53269, 1), (20000838920189041, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892802 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64OctF_401, prime_free64OctF_11069, prime_free64OctF_53269, prime_free64OctF_20000838920189041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892803 :
    Nat.totient 9458135072822578140090892803 = 6292887748497342370661753184 := by
  rw [← show
    ((([(3, 1), (503, 1), (15040590709, 1), (416726749916363, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892803 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64OctF_503, prime_free64OctF_15040590709, prime_free64OctF_416726749916363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892804 :
    Nat.totient 9458135072822578140090892804 = 4729045037719437242015215104 := by
  rw [← show
    ((([(2, 2), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892804 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892805 :
    Nat.totient 9458135072822578140090892805 = 7566418412949891821679408960 := by
  rw [← show
    ((([(5, 1), (85243, 1), (18480383, 1), (23255671, 1), (51634139, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892805 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64OctF_85243, prime_free64OctF_18480383, prime_free64OctF_23255671, prime_free64OctF_51634139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892806 :
    Nat.totient 9458135072822578140090892806 = 3152711690940859380030297600 := by
  rw [← show
    ((([(2, 1), (3, 1), (1576355845470429690015148801, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892806 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64OctF_1576355845470429690015148801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892807 :
    Nat.totient 9458135072822578140090892807 = 8004353009181117700935702528 := by
  rw [← show
    ((([(7, 1), (79, 1), (1272241326337, 1), (13443454509487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892807 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_79, prime_free64OctF_1272241326337, prime_free64OctF_13443454509487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892808 :
    Nat.totient 9458135072822578140090892808 = 4682219311413182558003904768 := by
  rw [← show
    ((([(2, 3), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892808 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892809 :
    Nat.totient 9458135072822578140090892809 = 6265253988266276981853813888 := by
  rw [← show
    ((([(3, 2), (227, 1), (509, 1), (106363, 1), (85512338798115589, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892809 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_227, prime_free64OctF_509, prime_free64OctF_106363, prime_free64OctF_85512338798115589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892810 :
    Nat.totient 9458135072822578140090892810 = 3744196689785619569559904000 := by
  rw [← show
    ((([(2, 1), (5, 1), (107, 1), (1013, 1), (144417341, 1), (60421700572451, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892810 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_107, prime_free64OctF_1013, prime_free64OctF_144417341, prime_free64OctF_60421700572451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892811 :
    Nat.totient 9458135072822578140090892811 = 8598203787169303446000107520 := by
  rw [← show
    ((([(11, 1), (85313, 1), (219959393, 1), (45820001621089, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892811 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_free64OctF_85313, prime_free64OctF_219959393, prime_free64OctF_45820001621089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892812 :
    Nat.totient 9458135072822578140090892812 = 3143099458521797824288512000 := by
  rw [← show
    ((([(2, 2), (3, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892812 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892813 :
    Nat.totient 9458135072822578140090892813 = 8697820469346636113771688960 := by
  rw [← show
    ((([(13, 1), (307, 1), (2011, 1), (100888969, 1), (11680677399577, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892813 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_t64_307, prime_free64OctF_2011, prime_free64OctF_100888969, prime_free64OctF_11680677399577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892814 :
    Nat.totient 9458135072822578140090892814 = 4049757401400441527193596952 := by
  rw [← show
    ((([(2, 1), (7, 1), (1087, 1), (621509730110564998034623, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892814 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64OctF_1087, prime_free64OctF_621509730110564998034623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892815 :
    Nat.totient 9458135072822578140090892815 = 5044262926251492700075547904 := by
  rw [← show
    ((([(3, 1), (5, 1), (66569, 1), (1596046247, 1), (5934672374047, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892815 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64OctF_66569, prime_free64OctF_1596046247, prime_free64OctF_5934672374047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892816 :
    Nat.totient 9458135072822578140090892816 = 4729067532543297963057648800 := by
  rw [← show
    ((([(2, 4), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892816 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892817 :
    Nat.totient 9458135072822578140090892817 = 8889066415381478401011130368 := by
  rw [← show
    ((([(17, 1), (709, 1), (58337, 1), (13451362101445396397, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892817 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_free64OctF_709, prime_free64OctF_58337, prime_free64OctF_13451362101445396397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892818 :
    Nat.totient 9458135072822578140090892818 = 3152711690940859380030297600 := by
  rw [← show
    ((([(2, 1), (3, 2), (525451948490143230005049601, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892818 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64OctF_525451948490143230005049601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892819 :
    Nat.totient 9458135072822578140090892819 = 8960338490019463528833605472 := by
  rw [← show
    ((([(19, 1), (390056504429, 1), (1276216592026469, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892819 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_free64OctF_390056504429, prime_free64OctF_1276216592026469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892820 :
    Nat.totient 9458135072822578140090892820 = 3766550734750699236795076224 := by
  rw [← show
    ((([(2, 2), (5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892820 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892821 :
    Nat.totient 9458135072822578140090892821 = 5404648613041473222909081600 := by
  rw [← show
    ((([(3, 1), (7, 1), (450387384420122768575756801, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892821 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_free64OctF_450387384420122768575756801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892822 :
    Nat.totient 9458135072822578140090892822 = 4298380879342397520174606720 := by
  rw [← show
    ((([(2, 1), (11, 2), (5573, 1), (3198253273, 1), (2192745608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892822 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_free64OctF_5573, prime_free64OctF_3198253273, prime_free64OctF_2192745608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892823 :
    Nat.totient 9458135072822578140090892823 = 8980875956167932020041873024 := by
  rw [← show
    ((([(23, 1), (137, 1), (3001629664494629685842873, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892823 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_137, prime_free64OctF_3001629664494629685842873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892824 :
    Nat.totient 9458135072822578140090892824 = 3152711690940859380030297600 := by
  rw [← show
    ((([(2, 3), (3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892824 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892825 :
    Nat.totient 9458135072822578140090892825 = 7520087763422123478256314000 := by
  rw [← show
    ((([(5, 2), (163, 1), (2321014741796951690819851, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892825 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_163, prime_free64OctF_2321014741796951690819851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892826 :
    Nat.totient 9458135072822578140090892826 = 4347901504515435859680150000 := by
  rw [← show
    ((([(2, 1), (13, 1), (251, 1), (1449300501505145286560051, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892826 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_251, prime_free64OctF_1449300501505145286560051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892827 :
    Nat.totient 9458135072822578140090892827 = 6305423381881718760060595056 := by
  rw [← show
    ((([(3, 5), (38922366554825424444818489, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892827 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64OctF_38922366554825424444818489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892828 :
    Nat.totient 9458135072822578140090892828 = 4053444895365943559296683504 := by
  rw [← show
    ((([(2, 2), (7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892828 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892829 :
    Nat.totient 9458135072822578140090892829 = 9131530408889049194550277936 := by
  rw [← show
    ((([(29, 1), (19763, 1), (16502686268178916959227, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892829 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_free64OctF_19763, prime_free64OctF_16502686268178916959227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892830 :
    Nat.totient 9458135072822578140090892830 = 2522022553179878183696046720 := by
  rw [← show
    ((([(2, 1), (3, 1), (5, 1), (22397, 1), (73771, 1), (190813341386997503, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892830 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_free64OctF_22397, prime_free64OctF_73771, prime_free64OctF_190813341386997503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892831 :
    Nat.totient 9458135072822578140090892831 = 9135938550966438558512954880 := by
  rw [← show
    ((([(31, 1), (547, 1), (25307, 1), (7487737, 1), (2943508165337, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892831 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_free64OctF_547, prime_free64OctF_25307, prime_free64OctF_7487737, prime_free64OctF_2943508165337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892832 :
    Nat.totient 9458135072822578140090892832 = 4729067310472396597300764672 := by
  rw [← show
    ((([(2, 5), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892832 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892833 :
    Nat.totient 9458135072822578140090892833 = 5731495482304186652590848000 := by
  rw [← show
    ((([(3, 1), (11, 1), (8101, 1), (64859654689, 1), (545479341709, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892833 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_free64OctF_8101, prime_free64OctF_64859654689, prime_free64OctF_545479341709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892834 :
    Nat.totient 9458135072822578140090892834 = 4387034880091442101345320960 := by
  rw [← show
    ((([(2, 1), (17, 1), (73, 1), (1609, 1), (29021, 1), (2685877, 1), (30384297329, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892834 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_73, prime_free64OctF_1609, prime_free64OctF_29021, prime_free64OctF_2685877, prime_free64OctF_30384297329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892835 :
    Nat.totient 9458135072822578140090892835 = 6485424168252302859488640000 := by
  rw [← show
    ((([(5, 1), (7, 1), (54287, 1), (193451, 1), (5530901, 1), (4652375513, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892835 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_free64OctF_54287, prime_free64OctF_193451, prime_free64OctF_5530901, prime_free64OctF_4652375513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892836 :
    Nat.totient 9458135072822578140090892836 = 3096409659294088452765542400 := by
  rw [← show
    ((([(2, 2), (3, 2), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892836 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_67, prime_t64_491, prime_t64_1061, prime_t64_9492089, prime_lucas_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892837 :
    Nat.totient 9458135072822578140090892837 = 9202503571738770533393366208 := by
  rw [← show
    ((([(37, 1), (2351599, 1), (3974227, 1), (27351922138837, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892837 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_free64OctF_2351599, prime_free64OctF_3974227, prime_free64OctF_27351922138837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892838 :
    Nat.totient 9458135072822578140090892838 = 4470467654769242318905337856 := by
  rw [← show
    ((([(2, 1), (19, 1), (463, 1), (177409, 1), (3030158014634483503, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892838 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_free64OctF_463, prime_free64OctF_177409, prime_free64OctF_3030158014634483503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892839 :
    Nat.totient 9458135072822578140090892839 = 5798753673472006729297850112 := by
  rw [← show
    ((([(3, 1), (13, 2), (269, 1), (69349809527745966433433, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892839 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_t64_269, prime_free64OctF_69349809527745966433433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892840 :
    Nat.totient 9458135072822578140090892840 = 3783254023086273327295674432 := by
  rw [← show
    ((([(2, 3), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892840 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892841 :
    Nat.totient 9458135072822578140090892841 = 9118910388684245109645888000 := by
  rw [← show
    ((([(41, 1), (109, 1), (383, 1), (834859, 1), (18321287, 1), (361266151, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892841 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_109, prime_t64_383, prime_free64OctF_834859, prime_free64OctF_18321287, prime_free64OctF_361266151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892842 :
    Nat.totient 9458135072822578140090892842 = 2702324306512326689345606448 := by
  rw [← show
    ((([(2, 1), (3, 1), (7, 1), (321473185079, 1), (700505369226119, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892842 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_free64OctF_321473185079, prime_free64OctF_700505369226119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892843 :
    Nat.totient 9458135072822578140090892843 = 9224197704901156185626473440 := by
  rw [← show
    ((([(43, 1), (661, 1), (1973467, 1), (168618696733348423, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892843 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_661, prime_free64OctF_1973467, prime_free64OctF_168618696733348423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892844 :
    Nat.totient 9458135072822578140090892844 = 4299152305828444609132224000 := by
  rw [← show
    ((([(2, 2), (11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892844 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_lucas_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892845 :
    Nat.totient 9458135072822578140090892845 = 5041350646922954404494574848 := by
  rw [← show
    ((([(3, 2), (5, 1), (2803, 1), (4243, 1), (17672454355456607929, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892845 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64OctF_2803, prime_free64OctF_4243, prime_free64OctF_17672454355456607929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892846 :
    Nat.totient 9458135072822578140090892846 = 4406013387276116717441635680 := by
  rw [← show
    ((([(2, 1), (23, 1), (71, 1), (83, 1), (34890825049700005681357, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892846 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_71, prime_t64_83, prime_free64OctF_34890825049700005681357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892847 :
    Nat.totient 9458135072822578140090892847 = 9217024555176450862370287360 := by
  rw [← show
    ((([(47, 1), (233, 1), (64439, 1), (6643181, 1), (2017561841483, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892847 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_233, prime_free64OctF_64439, prime_free64OctF_6643181, prime_free64OctF_2017561841483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892848 :
    Nat.totient 9458135072822578140090892848 = 3144933657121987422886215168 := by
  rw [← show
    ((([(2, 4), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892848 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892849 :
    Nat.totient 9458135072822578140090892849 = 8106179153979338060134746240 := by
  rw [← show
    ((([(7, 2), (10739, 1), (212573, 1), (11239603, 1), (7522921261, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892849 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64OctF_10739, prime_free64OctF_212573, prime_free64OctF_11239603, prime_free64OctF_7522921261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892850 :
    Nat.totient 9458135072822578140090892850 = 3783253996622399876788598720 := by
  rw [← show
    ((([(2, 1), (5, 2), (116384069, 1), (1625331568846003853, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892850 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64OctF_116384069, prime_free64OctF_1625331568846003853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892851 :
    Nat.totient 9458135072822578140090892851 = 5927558894805335355723118080 := by
  rw [← show
    ((([(3, 1), (17, 1), (853, 1), (10437455471, 1), (20830115065427, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892851 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_free64OctF_853, prime_free64OctF_10437455471, prime_free64OctF_20830115065427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892852 :
    Nat.totient 9458135072822578140090892852 = 4365293110532487154920609888 := by
  rw [← show
    ((([(2, 2), (13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892852 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_lucas_4887540332063, prime_lucas_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892853 :
    Nat.totient 9458135072822578140090892853 = 9184006524735507060853770240 := by
  rw [← show
    ((([(53, 1), (97, 1), (1446019, 1), (816013327, 1), (1559145541, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892853 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_t64_97, prime_free64OctF_1446019, prime_free64OctF_816013327, prime_free64OctF_1559145541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892854 :
    Nat.totient 9458135072822578140090892854 = 3152605599757666565836538976 := by
  rw [← show
    ((([(2, 1), (3, 3), (29717, 1), (5893954621823010734653, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892854 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64OctF_29717, prime_free64OctF_5893954621823010734653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892855 :
    Nat.totient 9458135072822578140090892855 = 6878643689325511374611558400 := by
  rw [← show
    ((([(5, 1), (11, 1), (171966092233137784365288961, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892855 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_free64OctF_171966092233137784365288961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892856 :
    Nat.totient 9458135072822578140090892856 = 4044693647204004540427678080 := by
  rw [← show
    ((([(2, 3), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892856 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892857 :
    Nat.totient 9458135072822578140090892857 = 5973558993360082777519740672 := by
  rw [← show
    ((([(3, 1), (19, 1), (4294706473193, 1), (38636445888857, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892857 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_free64OctF_4294706473193, prime_free64OctF_38636445888857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892858 :
    Nat.totient 9458135072822578140090892858 = 4565995948142389138240307200 := by
  rw [← show
    ((([(2, 1), (29, 1), (15535361, 1), (10496781784408483841, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892858 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_free64OctF_15535361, prime_free64OctF_10496781784408483841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892859 :
    Nat.totient 9458135072822578140090892859 = 9297827694484085827825205632 := by
  rw [← show
    ((([(59, 1), (2201786969, 1), (72807849429885929, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892859 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_free64OctF_2201786969, prime_free64OctF_72807849429885929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892860 :
    Nat.totient 9458135072822578140090892860 = 2522165306138967560477737024 := by
  rw [← show
    ((([(2, 2), (3, 1), (5, 1), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892860 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_623279, prime_lucas_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892861 :
    Nat.totient 9458135072822578140090892861 = 9234588202083860980549248000 := by
  rw [← show
    ((([(61, 1), (181, 1), (631, 1), (3793, 1), (357919120937944987, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892861 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_free64OctF_181, prime_free64OctF_631, prime_free64OctF_3793, prime_free64OctF_357919120937944987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892862 :
    Nat.totient 9458135072822578140090892862 = 4576516970720602325850432000 := by
  rw [← show
    ((([(2, 1), (31, 1), (152550565690686744195014401, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892862 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_free64OctF_152550565690686744195014401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892863 :
    Nat.totient 9458135072822578140090892863 = 5404616747324769068751184272 := by
  rw [← show
    ((([(3, 2), (7, 1), (169607, 1), (885158797337615327543, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892863 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_free64OctF_169607, prime_free64OctF_885158797337615327543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892864 :
    Nat.totient 9458135072822578140090892864 = 4704308003834607887353205760 := by
  rw [← show
    ((([(2, 6), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892864 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892865 :
    Nat.totient 9458135072822578140090892865 = 6984463912300853844742950912 := by
  rw [← show
    ((([(5, 1), (13, 1), (1379089, 1), (105511515465003771889, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892865 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_free64OctF_1379089, prime_free64OctF_105511515465003771889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892866 :
    Nat.totient 9458135072822578140090892866 = 2844237220717778503188480000 := by
  rw [← show
    ((([(2, 1), (3, 1), (11, 1), (293, 1), (313, 1), (1249, 1), (4201, 1), (297806723575661, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892866 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_free64OctF_293, prime_free64OctF_313, prime_free64OctF_1249, prime_free64OctF_4201, prime_free64OctF_297806723575661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892867 :
    Nat.totient 9458135072822578140090892867 = 9451507087487734006846258720 := by
  rw [← show
    ((([(1427, 1), (6627985334844133244632721, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892867 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64OctF_1427, prime_free64OctF_6627985334844133244632721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892868 :
    Nat.totient 9458135072822578140090892868 = 4427301007024085332608860160 := by
  rw [← show
    ((([(2, 2), (17, 1), (229, 1), (1669, 1), (2963, 1), (108608761, 1), (1130858507, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892868 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_229, prime_t64_1669, prime_t64_2963, prime_lucas_108608761, prime_lucas_1130858507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892869 :
    Nat.totient 9458135072822578140090892869 = 6031274539191209248753612800 := by
  rw [← show
    ((([(3, 1), (23, 1), (137074421345254755653491201, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892869 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_free64OctF_137074421345254755653491201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892870 :
    Nat.totient 9458135072822578140090892870 = 3242758483711376322453171168 := by
  rw [← show
    ((([(2, 1), (5, 1), (7, 1), (105683, 1), (1278504729483803739227, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892870 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_free64OctF_105683, prime_free64OctF_1278504729483803739227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892871 :
    Nat.totient 9458135072822578140090892871 = 9458135056718383453089864192 := by
  rw [← show
    ((([(1053289273, 1), (1814030879, 1), (4950090913, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892871 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64OctF_1053289273, prime_free64OctF_1814030879, prime_free64OctF_4950090913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892872 :
    Nat.totient 9458135072822578140090892872 = 3152711690940859380030297600 := by
  rw [← show
    ((([(2, 3), (3, 2), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892872 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892873 :
    Nat.totient 9458135072822578140090892873 = 9441743157618379564458152448 := by
  rw [← show
    ((([(577, 1), (16391915204198575632739849, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892873 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64OctF_577, prime_free64OctF_16391915204198575632739849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892874 :
    Nat.totient 9458135072822578140090892874 = 4584628896777536124127345920 := by
  rw [← show
    ((([(2, 1), (37, 1), (277, 1), (310627, 1), (21263909, 1), (69857287091, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892874 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_free64OctF_277, prime_free64OctF_310627, prime_free64OctF_21263909, prime_free64OctF_69857287091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892875 :
    Nat.totient 9458135072822578140090892875 = 5044015739459462002492032000 := by
  rw [← show
    ((([(3, 1), (5, 3), (15619, 1), (1160118241, 1), (1391934386639, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892875 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64OctF_15619, prime_free64OctF_1160118241, prime_free64OctF_1391934386639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892876 :
    Nat.totient 9458135072822578140090892876 = 4431440825772889578928128000 := by
  rw [← show
    ((([(2, 2), (19, 1), (149, 1), (349, 1), (1213, 1), (2897, 1), (6151, 1), (110719776691, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892876 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_149, prime_t64_349, prime_t64_1213, prime_t64_2897, prime_t64_6151, prime_lucas_110719776691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892877 :
    Nat.totient 9458135072822578140090892877 = 7369975318109024949827262720 := by
  rw [← show
    ((([(7, 1), (11, 1), (116408777, 1), (1055186096695009913, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892877 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_free64OctF_116408777, prime_free64OctF_1055186096695009913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892878 :
    Nat.totient 9458135072822578140090892878 = 2910195407022331735412582400 := by
  rw [← show
    ((([(2, 1), (3, 1), (13, 1), (121258141959263822308857601, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892878 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_free64OctF_121258141959263822308857601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892879 :
    Nat.totient 9458135072822578140090892879 = 9327327049906790880888890496 := by
  rw [← show
    ((([(113, 1), (199, 1), (57769814959, 1), (7280697974663, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892879 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_113, prime_free64OctF_199, prime_free64OctF_57769814959, prime_free64OctF_7280697974663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892880 :
    Nat.totient 9458135072822578140090892880 = 3745796068444585402016192000 := by
  rw [← show
    ((([(2, 4), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892880 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892881 :
    Nat.totient 9458135072822578140090892881 = 6302805753175003744969996800 := by
  rw [← show
    ((([(3, 3), (2411, 1), (2675633, 1), (54302271113539481, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892881 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64OctF_2411, prime_free64OctF_2675633, prime_free64OctF_54302271113539481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892882 :
    Nat.totient 9458135072822578140090892882 = 4544255915426801429728604160 := by
  rw [← show
    ((([(2, 1), (41, 1), (89, 1), (263, 1), (16823, 1), (344213, 1), (850971844357, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892882 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_t64_89, prime_t64_263, prime_free64OctF_16823, prime_free64OctF_344213, prime_free64OctF_850971844357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892883 :
    Nat.totient 9458135072822578140090892883 = 9448394459977240778463609840 := by
  rw [← show
    ((([(971, 1), (9740612845337361627282073, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892883 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64OctF_971, prime_free64OctF_9740612845337361627282073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892884 :
    Nat.totient 9458135072822578140090892884 = 2701498415173157803881332736 := by
  rw [← show
    ((([(2, 2), (3, 1), (7, 1), (4787, 1), (10337, 1), (269456833, 1), (8444599963, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892884 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_4787, prime_t64_10337, prime_lucas_269456833, prime_lucas_8444599963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892885 :
    Nat.totient 9458135072822578140090892885 = 7121392369481090252202585088 := by
  rw [← show
    ((([(5, 1), (17, 1), (263957, 1), (421554182413516022333, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892885 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_free64OctF_263957, prime_free64OctF_421554182413516022333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892886 :
    Nat.totient 9458135072822578140090892886 = 4560618365248178465243889696 := by
  rw [← show
    ((([(2, 1), (43, 1), (79, 1), (3322747, 1), (418969776239939677, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892886 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_t64_79, prime_free64OctF_3322747, prime_free64OctF_418969776239939677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892887 :
    Nat.totient 9458135072822578140090892887 = 6087994719974816614471721600 := by
  rw [← show
    ((([(3, 1), (29, 1), (22595981, 1), (4811218253340714821, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892887 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_free64OctF_22595981, prime_free64OctF_4811218253340714821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64OctF_9458135072822578140090892888 :
    Nat.totient 9458135072822578140090892888 = 4299152305828444609132224000 := by
  rw [← show
    ((([(2, 3), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 9458135072822578140090892888 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- A free-position kill ten below eight times `periodLcm 64`. -/
theorem freeKill_64OctF :
    certifiedKill 1 9458135072822578140090892790 97 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free64OctF_9458135072822578140090892791,
    phi_free64OctF_9458135072822578140090892792,
    phi_free64OctF_9458135072822578140090892793,
    phi_free64OctF_9458135072822578140090892794,
    phi_free64OctF_9458135072822578140090892795,
    phi_free64OctF_9458135072822578140090892796,
    phi_free64OctF_9458135072822578140090892797,
    phi_free64OctF_9458135072822578140090892798,
    phi_free64OctF_9458135072822578140090892799,
    phi_free64OctF_9458135072822578140090892800,
    phi_free64OctF_9458135072822578140090892801,
    phi_free64OctF_9458135072822578140090892802,
    phi_free64OctF_9458135072822578140090892803,
    phi_free64OctF_9458135072822578140090892804,
    phi_free64OctF_9458135072822578140090892805,
    phi_free64OctF_9458135072822578140090892806,
    phi_free64OctF_9458135072822578140090892807,
    phi_free64OctF_9458135072822578140090892808,
    phi_free64OctF_9458135072822578140090892809,
    phi_free64OctF_9458135072822578140090892810,
    phi_free64OctF_9458135072822578140090892811,
    phi_free64OctF_9458135072822578140090892812,
    phi_free64OctF_9458135072822578140090892813,
    phi_free64OctF_9458135072822578140090892814,
    phi_free64OctF_9458135072822578140090892815,
    phi_free64OctF_9458135072822578140090892816,
    phi_free64OctF_9458135072822578140090892817,
    phi_free64OctF_9458135072822578140090892818,
    phi_free64OctF_9458135072822578140090892819,
    phi_free64OctF_9458135072822578140090892820,
    phi_free64OctF_9458135072822578140090892821,
    phi_free64OctF_9458135072822578140090892822,
    phi_free64OctF_9458135072822578140090892823,
    phi_free64OctF_9458135072822578140090892824,
    phi_free64OctF_9458135072822578140090892825,
    phi_free64OctF_9458135072822578140090892826,
    phi_free64OctF_9458135072822578140090892827,
    phi_free64OctF_9458135072822578140090892828,
    phi_free64OctF_9458135072822578140090892829,
    phi_free64OctF_9458135072822578140090892830,
    phi_free64OctF_9458135072822578140090892831,
    phi_free64OctF_9458135072822578140090892832,
    phi_free64OctF_9458135072822578140090892833,
    phi_free64OctF_9458135072822578140090892834,
    phi_free64OctF_9458135072822578140090892835,
    phi_free64OctF_9458135072822578140090892836,
    phi_free64OctF_9458135072822578140090892837,
    phi_free64OctF_9458135072822578140090892838,
    phi_free64OctF_9458135072822578140090892839,
    phi_free64OctF_9458135072822578140090892840,
    phi_free64OctF_9458135072822578140090892841,
    phi_free64OctF_9458135072822578140090892842,
    phi_free64OctF_9458135072822578140090892843,
    phi_free64OctF_9458135072822578140090892844,
    phi_free64OctF_9458135072822578140090892845,
    phi_free64OctF_9458135072822578140090892846,
    phi_free64OctF_9458135072822578140090892847,
    phi_free64OctF_9458135072822578140090892848,
    phi_free64OctF_9458135072822578140090892849,
    phi_free64OctF_9458135072822578140090892850,
    phi_free64OctF_9458135072822578140090892851,
    phi_free64OctF_9458135072822578140090892852,
    phi_free64OctF_9458135072822578140090892853,
    phi_free64OctF_9458135072822578140090892854,
    phi_free64OctF_9458135072822578140090892855,
    phi_free64OctF_9458135072822578140090892856,
    phi_free64OctF_9458135072822578140090892857,
    phi_free64OctF_9458135072822578140090892858,
    phi_free64OctF_9458135072822578140090892859,
    phi_free64OctF_9458135072822578140090892860,
    phi_free64OctF_9458135072822578140090892861,
    phi_free64OctF_9458135072822578140090892862,
    phi_free64OctF_9458135072822578140090892863,
    phi_free64OctF_9458135072822578140090892864,
    phi_free64OctF_9458135072822578140090892865,
    phi_free64OctF_9458135072822578140090892866,
    phi_free64OctF_9458135072822578140090892867,
    phi_free64OctF_9458135072822578140090892868,
    phi_free64OctF_9458135072822578140090892869,
    phi_free64OctF_9458135072822578140090892870,
    phi_free64OctF_9458135072822578140090892871,
    phi_free64OctF_9458135072822578140090892872,
    phi_free64OctF_9458135072822578140090892873,
    phi_free64OctF_9458135072822578140090892874,
    phi_free64OctF_9458135072822578140090892875,
    phi_free64OctF_9458135072822578140090892876,
    phi_free64OctF_9458135072822578140090892877,
    phi_free64OctF_9458135072822578140090892878,
    phi_free64OctF_9458135072822578140090892879,
    phi_free64OctF_9458135072822578140090892880,
    phi_free64OctF_9458135072822578140090892881,
    phi_free64OctF_9458135072822578140090892882,
    phi_free64OctF_9458135072822578140090892883,
    phi_free64OctF_9458135072822578140090892884,
    phi_free64OctF_9458135072822578140090892885,
    phi_free64OctF_9458135072822578140090892886,
    phi_free64OctF_9458135072822578140090892887,
    phi_free64OctF_9458135072822578140090892888]

end TotientTailPeriodKiller
end Erdos249257
