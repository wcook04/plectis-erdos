import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
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
  prime_t64_223
  prime_t64_229
  prime_t64_233
  prime_t64_251
  prime_t64_263
  prime_t64_269
  prime_t64_311
  prime_t64_383
  prime_t64_409
  prime_t64_421
  prime_t64_431
  prime_t64_461
  prime_t64_467
  prime_t64_641
  prime_t64_647
  prime_t64_673
  prime_t64_683
  prime_t64_719
  prime_t64_787
  prime_t64_859
  prime_t64_997
  prime_t64_1229
  prime_t64_1669
  prime_t64_1801
  prime_t64_3769
  prime_t64_5009
  prime_t64_45127
  prime_t64_20930737
  from Erdos249257.DiagonalPincerCertificatesT64

private theorem prime_free64ElevenI_127 : Nat.Prime 127 := by norm_num
private theorem prime_free64ElevenI_131 : Nat.Prime 131 := by norm_num
private theorem prime_free64ElevenI_151 : Nat.Prime 151 := by norm_num
private theorem prime_free64ElevenI_173 : Nat.Prime 173 := by norm_num
private theorem prime_free64ElevenI_181 : Nat.Prime 181 := by norm_num
private theorem prime_free64ElevenI_199 : Nat.Prime 199 := by norm_num
private theorem prime_free64ElevenI_211 : Nat.Prime 211 := by norm_num
private theorem prime_free64ElevenI_241 : Nat.Prime 241 := by norm_num
private theorem prime_free64ElevenI_257 : Nat.Prime 257 := by norm_num
private theorem prime_free64ElevenI_271 : Nat.Prime 271 := by norm_num
private theorem prime_free64ElevenI_277 : Nat.Prime 277 := by norm_num
private theorem prime_free64ElevenI_281 : Nat.Prime 281 := by norm_num
private theorem prime_free64ElevenI_331 : Nat.Prime 331 := by norm_num
private theorem prime_free64ElevenI_337 : Nat.Prime 337 := by norm_num
private theorem prime_free64ElevenI_347 : Nat.Prime 347 := by norm_num
private theorem prime_free64ElevenI_353 : Nat.Prime 353 := by norm_num
private theorem prime_free64ElevenI_373 : Nat.Prime 373 := by norm_num
private theorem prime_free64ElevenI_397 : Nat.Prime 397 := by norm_num
private theorem prime_free64ElevenI_401 : Nat.Prime 401 := by norm_num
private theorem prime_free64ElevenI_503 : Nat.Prime 503 := by norm_num
private theorem prime_free64ElevenI_509 : Nat.Prime 509 := by norm_num
private theorem prime_free64ElevenI_547 : Nat.Prime 547 := by norm_num
private theorem prime_free64ElevenI_569 : Nat.Prime 569 := by norm_num
private theorem prime_free64ElevenI_571 : Nat.Prime 571 := by norm_num
private theorem prime_free64ElevenI_587 : Nat.Prime 587 := by norm_num
private theorem prime_free64ElevenI_593 : Nat.Prime 593 := by norm_num
private theorem prime_free64ElevenI_631 : Nat.Prime 631 := by norm_num
private theorem prime_free64ElevenI_643 : Nat.Prime 643 := by norm_num
private theorem prime_free64ElevenI_653 : Nat.Prime 653 := by norm_num
private theorem prime_free64ElevenI_677 : Nat.Prime 677 := by norm_num
private theorem prime_free64ElevenI_691 : Nat.Prime 691 := by norm_num
private theorem prime_free64ElevenI_727 : Nat.Prime 727 := by norm_num
private theorem prime_free64ElevenI_773 : Nat.Prime 773 := by norm_num
private theorem prime_free64ElevenI_797 : Nat.Prime 797 := by norm_num
private theorem prime_free64ElevenI_809 : Nat.Prime 809 := by norm_num
private theorem prime_free64ElevenI_827 : Nat.Prime 827 := by norm_num
private theorem prime_free64ElevenI_857 : Nat.Prime 857 := by norm_num
private theorem prime_free64ElevenI_941 : Nat.Prime 941 := by norm_num
private theorem prime_free64ElevenI_953 : Nat.Prime 953 := by norm_num
private theorem prime_free64ElevenI_967 : Nat.Prime 967 := by norm_num
private theorem prime_free64ElevenI_977 : Nat.Prime 977 := by norm_num
private theorem prime_free64ElevenI_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_free64ElevenI_1033 : Nat.Prime 1033 := by norm_num
private theorem prime_free64ElevenI_1039 : Nat.Prime 1039 := by norm_num
private theorem prime_free64ElevenI_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_free64ElevenI_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_free64ElevenI_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_free64ElevenI_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_free64ElevenI_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_free64ElevenI_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_free64ElevenI_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_free64ElevenI_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_free64ElevenI_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_free64ElevenI_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_free64ElevenI_1307 : Nat.Prime 1307 := by norm_num
private theorem prime_free64ElevenI_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_free64ElevenI_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_free64ElevenI_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_free64ElevenI_1523 : Nat.Prime 1523 := by norm_num
private theorem prime_free64ElevenI_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_free64ElevenI_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_free64ElevenI_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_free64ElevenI_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_free64ElevenI_1627 : Nat.Prime 1627 := by norm_num
private theorem prime_free64ElevenI_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_free64ElevenI_1697 : Nat.Prime 1697 := by norm_num
private theorem prime_free64ElevenI_1987 : Nat.Prime 1987 := by norm_num
private theorem prime_free64ElevenI_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_free64ElevenI_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_free64ElevenI_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_free64ElevenI_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_free64ElevenI_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_free64ElevenI_2297 : Nat.Prime 2297 := by norm_num
private theorem prime_free64ElevenI_2351 : Nat.Prime 2351 := by norm_num
private theorem prime_free64ElevenI_2551 : Nat.Prime 2551 := by norm_num
private theorem prime_free64ElevenI_2557 : Nat.Prime 2557 := by norm_num
private theorem prime_free64ElevenI_2699 : Nat.Prime 2699 := by norm_num
private theorem prime_free64ElevenI_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_free64ElevenI_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_free64ElevenI_2887 : Nat.Prime 2887 := by norm_num
private theorem prime_free64ElevenI_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_free64ElevenI_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_free64ElevenI_3041 : Nat.Prime 3041 := by norm_num
private theorem prime_free64ElevenI_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_free64ElevenI_3361 : Nat.Prime 3361 := by norm_num
private theorem prime_free64ElevenI_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_free64ElevenI_3559 : Nat.Prime 3559 := by norm_num
private theorem prime_free64ElevenI_3637 : Nat.Prime 3637 := by norm_num
private theorem prime_free64ElevenI_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_free64ElevenI_3793 : Nat.Prime 3793 := by norm_num
private theorem prime_free64ElevenI_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_free64ElevenI_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_free64ElevenI_4073 : Nat.Prime 4073 := by norm_num
private theorem prime_free64ElevenI_4093 : Nat.Prime 4093 := by norm_num
private theorem prime_free64ElevenI_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_free64ElevenI_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_free64ElevenI_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_free64ElevenI_4451 : Nat.Prime 4451 := by norm_num
private theorem prime_free64ElevenI_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_free64ElevenI_4493 : Nat.Prime 4493 := by norm_num
private theorem prime_free64ElevenI_4549 : Nat.Prime 4549 := by norm_num
private theorem prime_free64ElevenI_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_free64ElevenI_4679 : Nat.Prime 4679 := by norm_num
private theorem prime_free64ElevenI_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_free64ElevenI_4969 : Nat.Prime 4969 := by norm_num
private theorem prime_free64ElevenI_4973 : Nat.Prime 4973 := by norm_num
private theorem prime_free64ElevenI_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_free64ElevenI_5171 : Nat.Prime 5171 := by norm_num
private theorem prime_free64ElevenI_5227 : Nat.Prime 5227 := by norm_num
private theorem prime_free64ElevenI_5471 : Nat.Prime 5471 := by norm_num
private theorem prime_free64ElevenI_5869 : Nat.Prime 5869 := by norm_num
private theorem prime_free64ElevenI_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_free64ElevenI_6133 : Nat.Prime 6133 := by norm_num
private theorem prime_free64ElevenI_6379 : Nat.Prime 6379 := by norm_num
private theorem prime_free64ElevenI_6427 : Nat.Prime 6427 := by norm_num
private theorem prime_free64ElevenI_6529 : Nat.Prime 6529 := by norm_num
private theorem prime_free64ElevenI_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_free64ElevenI_6661 : Nat.Prime 6661 := by norm_num
private theorem prime_free64ElevenI_6977 : Nat.Prime 6977 := by norm_num
private theorem prime_free64ElevenI_7193 : Nat.Prime 7193 := by norm_num
private theorem prime_free64ElevenI_7213 : Nat.Prime 7213 := by norm_num
private theorem prime_free64ElevenI_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_free64ElevenI_7457 : Nat.Prime 7457 := by norm_num
private theorem prime_free64ElevenI_7867 : Nat.Prime 7867 := by norm_num
private theorem prime_free64ElevenI_8231 : Nat.Prime 8231 := by norm_num
private theorem prime_free64ElevenI_8623 : Nat.Prime 8623 := by norm_num
private theorem prime_free64ElevenI_8669 : Nat.Prime 8669 := by norm_num
private theorem prime_free64ElevenI_8779 : Nat.Prime 8779 := by norm_num
private theorem prime_free64ElevenI_8951 : Nat.Prime 8951 := by norm_num
private theorem prime_free64ElevenI_9029 : Nat.Prime 9029 := by norm_num
private theorem prime_free64ElevenI_9151 : Nat.Prime 9151 := by norm_num
private theorem prime_free64ElevenI_9257 : Nat.Prime 9257 := by norm_num
private theorem prime_free64ElevenI_9619 : Nat.Prime 9619 := by norm_num
private theorem prime_free64ElevenI_9721 : Nat.Prime 9721 := by norm_num
private theorem prime_free64ElevenI_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_free64ElevenI_10691 : Nat.Prime 10691 := by norm_num
private theorem prime_free64ElevenI_10987 : Nat.Prime 10987 := by norm_num
private theorem prime_free64ElevenI_11717 : Nat.Prime 11717 := by norm_num
private theorem prime_free64ElevenI_11933 : Nat.Prime 11933 := by norm_num
private theorem prime_free64ElevenI_12049 : Nat.Prime 12049 := by norm_num
private theorem prime_free64ElevenI_12211 : Nat.Prime 12211 := by norm_num
private theorem prime_free64ElevenI_12227 : Nat.Prime 12227 := by norm_num
private theorem prime_free64ElevenI_12721 : Nat.Prime 12721 := by norm_num
private theorem prime_free64ElevenI_12743 : Nat.Prime 12743 := by norm_num
private theorem prime_free64ElevenI_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_free64ElevenI_13397 : Nat.Prime 13397 := by norm_num
private theorem prime_free64ElevenI_13457 : Nat.Prime 13457 := by norm_num
private theorem prime_free64ElevenI_14423 : Nat.Prime 14423 := by norm_num
private theorem prime_free64ElevenI_14563 : Nat.Prime 14563 := by norm_num
private theorem prime_free64ElevenI_16073 : Nat.Prime 16073 := by norm_num
private theorem prime_free64ElevenI_16987 : Nat.Prime 16987 := by norm_num
private theorem prime_free64ElevenI_17099 : Nat.Prime 17099 := by norm_num
private theorem prime_free64ElevenI_17749 : Nat.Prime 17749 := by norm_num
private theorem prime_free64ElevenI_18217 : Nat.Prime 18217 := by norm_num
private theorem prime_free64ElevenI_18787 : Nat.Prime 18787 := by norm_num
private theorem prime_free64ElevenI_19427 : Nat.Prime 19427 := by norm_num
private theorem prime_free64ElevenI_19553 : Nat.Prime 19553 := by norm_num
private theorem prime_free64ElevenI_19841 : Nat.Prime 19841 := by norm_num
private theorem prime_free64ElevenI_20021 : Nat.Prime 20021 := by norm_num
private theorem prime_free64ElevenI_22511 : Nat.Prime 22511 := by norm_num
private theorem prime_free64ElevenI_22619 : Nat.Prime 22619 := by norm_num
private theorem prime_free64ElevenI_24077 : Nat.Prime 24077 := by norm_num
private theorem prime_free64ElevenI_25439 : Nat.Prime 25439 := by norm_num
private theorem prime_free64ElevenI_27077 : Nat.Prime 27077 := by norm_num
private theorem prime_free64ElevenI_27361 : Nat.Prime 27361 := by norm_num
private theorem prime_free64ElevenI_28297 : Nat.Prime 28297 := by norm_num
private theorem prime_free64ElevenI_28351 : Nat.Prime 28351 := by norm_num
private theorem prime_free64ElevenI_28687 : Nat.Prime 28687 := by norm_num
private theorem prime_free64ElevenI_29131 : Nat.Prime 29131 := by norm_num
private theorem prime_free64ElevenI_30203 : Nat.Prime 30203 := by norm_num
private theorem prime_free64ElevenI_31159 : Nat.Prime 31159 := by norm_num
private theorem prime_free64ElevenI_31891 : Nat.Prime 31891 := by norm_num
private theorem prime_free64ElevenI_32377 : Nat.Prime 32377 := by norm_num
private theorem prime_free64ElevenI_32531 : Nat.Prime 32531 := by norm_num
private theorem prime_free64ElevenI_32843 : Nat.Prime 32843 := by norm_num
private theorem prime_free64ElevenI_32869 : Nat.Prime 32869 := by norm_num
private theorem prime_free64ElevenI_34667 : Nat.Prime 34667 := by norm_num
private theorem prime_free64ElevenI_35543 : Nat.Prime 35543 := by norm_num
private theorem prime_free64ElevenI_35569 : Nat.Prime 35569 := by norm_num
private theorem prime_free64ElevenI_36899 : Nat.Prime 36899 := by norm_num
private theorem prime_free64ElevenI_36973 : Nat.Prime 36973 := by norm_num
private theorem prime_free64ElevenI_37547 : Nat.Prime 37547 := by norm_num
private theorem prime_free64ElevenI_37579 : Nat.Prime 37579 := by norm_num
private theorem prime_free64ElevenI_37967 : Nat.Prime 37967 := by norm_num
private theorem prime_free64ElevenI_38393 : Nat.Prime 38393 := by norm_num
private theorem prime_free64ElevenI_39113 : Nat.Prime 39113 := by norm_num
private theorem prime_free64ElevenI_40627 : Nat.Prime 40627 := by norm_num
private theorem prime_free64ElevenI_41131 : Nat.Prime 41131 := by norm_num
private theorem prime_free64ElevenI_41737 : Nat.Prime 41737 := by norm_num
private theorem prime_free64ElevenI_43891 : Nat.Prime 43891 := by norm_num
private theorem prime_free64ElevenI_44101 : Nat.Prime 44101 := by norm_num
private theorem prime_free64ElevenI_46273 : Nat.Prime 46273 := by norm_num
private theorem prime_free64ElevenI_47659 : Nat.Prime 47659 := by norm_num
private theorem prime_free64ElevenI_48091 : Nat.Prime 48091 := by norm_num
private theorem prime_free64ElevenI_50627 : Nat.Prime 50627 := by norm_num
private theorem prime_free64ElevenI_54101 : Nat.Prime 54101 := by norm_num
private theorem prime_free64ElevenI_55217 : Nat.Prime 55217 := by norm_num
private theorem prime_free64ElevenI_55843 : Nat.Prime 55843 := by norm_num
private theorem prime_free64ElevenI_56659 : Nat.Prime 56659 := by norm_num
private theorem prime_free64ElevenI_57349 : Nat.Prime 57349 := by norm_num
private theorem prime_free64ElevenI_59159 : Nat.Prime 59159 := by norm_num
private theorem prime_free64ElevenI_59693 : Nat.Prime 59693 := by norm_num
private theorem prime_free64ElevenI_60353 : Nat.Prime 60353 := by norm_num
private theorem prime_free64ElevenI_64399 : Nat.Prime 64399 := by norm_num
private theorem prime_free64ElevenI_67901 : Nat.Prime 67901 := by norm_num
private theorem prime_free64ElevenI_68639 : Nat.Prime 68639 := by norm_num
private theorem prime_free64ElevenI_70879 : Nat.Prime 70879 := by norm_num
private theorem prime_free64ElevenI_72253 : Nat.Prime 72253 := by norm_num
private theorem prime_free64ElevenI_74687 : Nat.Prime 74687 := by norm_num
private theorem prime_free64ElevenI_76207 : Nat.Prime 76207 := by norm_num
private theorem prime_free64ElevenI_77951 : Nat.Prime 77951 := by norm_num
private theorem prime_free64ElevenI_78809 : Nat.Prime 78809 := by norm_num
private theorem prime_free64ElevenI_83459 : Nat.Prime 83459 := by norm_num
private theorem prime_free64ElevenI_85817 : Nat.Prime 85817 := by norm_num
private theorem prime_free64ElevenI_85889 : Nat.Prime 85889 := by norm_num
private theorem prime_free64ElevenI_89669 : Nat.Prime 89669 := by norm_num
private theorem prime_free64ElevenI_101267 : Nat.Prime 101267 := by norm_num
private theorem prime_free64ElevenI_104053 : Nat.Prime 104053 := by norm_num
private theorem prime_free64ElevenI_118373 : Nat.Prime 118373 := by norm_num
private theorem prime_free64ElevenI_119831 : Nat.Prime 119831 := by norm_num
private theorem prime_free64ElevenI_124171 : Nat.Prime 124171 := by norm_num
private theorem prime_free64ElevenI_129281 : Nat.Prime 129281 := by norm_num
private theorem prime_free64ElevenI_129853 : Nat.Prime 129853 := by norm_num
private theorem prime_free64ElevenI_132857 : Nat.Prime 132857 := by norm_num
private theorem prime_free64ElevenI_137909 : Nat.Prime 137909 := by norm_num
private theorem prime_free64ElevenI_138179 : Nat.Prime 138179 := by norm_num
private theorem prime_free64ElevenI_143419 : Nat.Prime 143419 := by norm_num
private theorem prime_free64ElevenI_144383 : Nat.Prime 144383 := by norm_num
private theorem prime_free64ElevenI_146059 : Nat.Prime 146059 := by norm_num
private theorem prime_free64ElevenI_147031 : Nat.Prime 147031 := by norm_num
private theorem prime_free64ElevenI_152041 : Nat.Prime 152041 := by norm_num
private theorem prime_free64ElevenI_154807 : Nat.Prime 154807 := by norm_num
private theorem prime_free64ElevenI_173059 : Nat.Prime 173059 := by norm_num
private theorem prime_free64ElevenI_198251 : Nat.Prime 198251 := by norm_num
private theorem prime_free64ElevenI_198851 : Nat.Prime 198851 := by norm_num
private theorem prime_free64ElevenI_221219 : Nat.Prime 221219 := by norm_num
private theorem prime_free64ElevenI_222419 : Nat.Prime 222419 := by norm_num
private theorem prime_free64ElevenI_230281 : Nat.Prime 230281 := by norm_num
private theorem prime_free64ElevenI_252767 : Nat.Prime 252767 := by norm_num
private theorem prime_free64ElevenI_259621 : Nat.Prime 259621 := by norm_num
private theorem prime_free64ElevenI_275339 : Nat.Prime 275339 := by norm_num
private theorem prime_free64ElevenI_283487 : Nat.Prime 283487 := by norm_num
private theorem prime_free64ElevenI_293179 : Nat.Prime 293179 := by norm_num
private theorem prime_free64ElevenI_316363 : Nat.Prime 316363 := by norm_num
private theorem prime_free64ElevenI_329519 : Nat.Prime 329519 := by norm_num
private theorem prime_free64ElevenI_346699 : Nat.Prime 346699 := by norm_num
private theorem prime_free64ElevenI_352813 : Nat.Prime 352813 := by norm_num
private theorem prime_free64ElevenI_378019 : Nat.Prime 378019 := by norm_num
private theorem prime_free64ElevenI_401887 : Nat.Prime 401887 := by norm_num
private theorem prime_free64ElevenI_432391 : Nat.Prime 432391 := by norm_num
private theorem prime_free64ElevenI_455471 : Nat.Prime 455471 := by norm_num
private theorem prime_free64ElevenI_470579 : Nat.Prime 470579 := by norm_num
private theorem prime_free64ElevenI_512047 : Nat.Prime 512047 := by norm_num
private theorem prime_free64ElevenI_514793 : Nat.Prime 514793 := by norm_num
private theorem prime_free64ElevenI_517469 : Nat.Prime 517469 := by norm_num
private theorem prime_free64ElevenI_524347 : Nat.Prime 524347 := by norm_num
private theorem prime_free64ElevenI_531337 : Nat.Prime 531337 := by norm_num
private theorem prime_free64ElevenI_535943 : Nat.Prime 535943 := by norm_num
private theorem prime_free64ElevenI_539633 : Nat.Prime 539633 := by norm_num
private theorem prime_free64ElevenI_565567 : Nat.Prime 565567 := by norm_num
private theorem prime_free64ElevenI_627787 : Nat.Prime 627787 := by norm_num
private theorem prime_free64ElevenI_643187 : Nat.Prime 643187 := by norm_num
private theorem prime_free64ElevenI_645481 : Nat.Prime 645481 := by norm_num
private theorem prime_free64ElevenI_706841 : Nat.Prime 706841 := by norm_num
private theorem prime_free64ElevenI_727781 : Nat.Prime 727781 := by norm_num
private theorem prime_free64ElevenI_756641 : Nat.Prime 756641 := by norm_num
private theorem prime_free64ElevenI_767813 : Nat.Prime 767813 := by norm_num
private theorem prime_free64ElevenI_810913 : Nat.Prime 810913 := by norm_num
private theorem prime_free64ElevenI_816353 : Nat.Prime 816353 := by norm_num
private theorem prime_free64ElevenI_834527 : Nat.Prime 834527 := by norm_num
private theorem prime_free64ElevenI_850351 : Nat.Prime 850351 := by norm_num
private theorem prime_free64ElevenI_895529 : Nat.Prime 895529 := by norm_num
private theorem prime_free64ElevenI_911903 : Nat.Prime 911903 := by norm_num
private theorem prime_free64ElevenI_940573 : Nat.Prime 940573 := by norm_num
private theorem prime_free64ElevenI_1009993 : Nat.Prime 1009993 := by norm_num
private theorem prime_free64ElevenI_1064669 : Nat.Prime 1064669 := by norm_num
private theorem prime_free64ElevenI_1079527 : Nat.Prime 1079527 := by norm_num
private theorem prime_free64ElevenI_1101371 : Nat.Prime 1101371 := by norm_num
private theorem prime_free64ElevenI_1108103 : Nat.Prime 1108103 := by norm_num
private theorem prime_free64ElevenI_1127981 : Nat.Prime 1127981 := by norm_num
private theorem prime_free64ElevenI_1231171 : Nat.Prime 1231171 := by norm_num
private theorem prime_free64ElevenI_1251703 : Nat.Prime 1251703 := by norm_num
private theorem prime_free64ElevenI_1284617 : Nat.Prime 1284617 := by norm_num
private theorem prime_free64ElevenI_1304419 : Nat.Prime 1304419 := by norm_num
private theorem prime_free64ElevenI_1344901 : Nat.Prime 1344901 := by norm_num
private theorem prime_free64ElevenI_1350521 : Nat.Prime 1350521 := by norm_num
private theorem prime_free64ElevenI_1356077 : Nat.Prime 1356077 := by norm_num
private theorem prime_free64ElevenI_1454477 : Nat.Prime 1454477 := by norm_num
private theorem prime_free64ElevenI_1794239 : Nat.Prime 1794239 := by norm_num
private theorem prime_free64ElevenI_1832513 : Nat.Prime 1832513 := by norm_num
private theorem prime_free64ElevenI_1883407 : Nat.Prime 1883407 := by norm_num
private theorem prime_free64ElevenI_1899647 : Nat.Prime 1899647 := by norm_num
private theorem prime_free64ElevenI_2139499 : Nat.Prime 2139499 := by norm_num
private theorem prime_free64ElevenI_2152009 : Nat.Prime 2152009 := by norm_num
private theorem prime_free64ElevenI_2395051 : Nat.Prime 2395051 := by norm_num
private theorem prime_free64ElevenI_2713289 : Nat.Prime 2713289 := by norm_num
private theorem prime_free64ElevenI_2719511 : Nat.Prime 2719511 := by norm_num
private theorem prime_free64ElevenI_2934583 : Nat.Prime 2934583 := by norm_num
private theorem prime_free64ElevenI_3022027 : Nat.Prime 3022027 := by norm_num
private theorem prime_free64ElevenI_3072847 : Nat.Prime 3072847 := by norm_num
private theorem prime_free64ElevenI_3312167 : Nat.Prime 3312167 := by norm_num
private theorem prime_free64ElevenI_3446959 : Nat.Prime 3446959 := by norm_num
private theorem prime_free64ElevenI_3707213 : Nat.Prime 3707213 := by norm_num
private theorem prime_free64ElevenI_3822619 : Nat.Prime 3822619 := by norm_num
private theorem prime_free64ElevenI_3951611 : Nat.Prime 3951611 := by norm_num
private theorem prime_free64ElevenI_4168501 : Nat.Prime 4168501 := by norm_num
private theorem prime_free64ElevenI_4663859 : Nat.Prime 4663859 := by norm_num
private theorem prime_free64ElevenI_4868909 : Nat.Prime 4868909 := by norm_num
private theorem prime_free64ElevenI_4885691 : Nat.Prime 4885691 := by norm_num
private theorem prime_free64ElevenI_5131963 : Nat.Prime 5131963 := by norm_num
private theorem prime_free64ElevenI_5191799 : Nat.Prime 5191799 := by norm_num
private theorem prime_free64ElevenI_5207243 : Nat.Prime 5207243 := by norm_num
private theorem prime_free64ElevenI_5225593 : Nat.Prime 5225593 := by norm_num
private theorem prime_free64ElevenI_5426387 : Nat.Prime 5426387 := by norm_num
private theorem prime_free64ElevenI_5853893 : Nat.Prime 5853893 := by norm_num
private theorem prime_free64ElevenI_6672769 : Nat.Prime 6672769 := by norm_num
private theorem prime_free64ElevenI_7622633 : Nat.Prime 7622633 := by norm_num
private theorem prime_free64ElevenI_8059837 : Nat.Prime 8059837 := by norm_num
private theorem prime_free64ElevenI_8103079 : Nat.Prime 8103079 := by norm_num
private theorem prime_free64ElevenI_8116909 : Nat.Prime 8116909 := by norm_num
private theorem prime_free64ElevenI_8917991 : Nat.Prime 8917991 := by norm_num
private theorem prime_free64ElevenI_9392503 : Nat.Prime 9392503 := by norm_num

private theorem prime_free64ElevenI_11218483 : Nat.Prime 11218483 := by
  have hfermat : (3 : ZMod 11218483) ^ (11218483 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11218483) ^ ((11218483 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11218483) ^ ((11218483 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11218483) ^ ((11218483 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11218483) ^ ((11218483 - 1) / 56659) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11218483 (3 : ZMod 11218483)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (56659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (56659, 1)] : List FactorBlock).map factorBlockValue).prod = 11218483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64ElevenI_56659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_11347241 : Nat.Prime 11347241 := by
  have hfermat : (6 : ZMod 11347241) ^ (11347241 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 11347241) ^ ((11347241 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 11347241) ^ ((11347241 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 11347241) ^ ((11347241 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 11347241) ^ ((11347241 - 1) / 9151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11347241 (6 : ZMod 11347241)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (31, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (31, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod = 11347241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_free64ElevenI_9151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_13664159 : Nat.Prime 13664159 := by
  have hfermat : (11 : ZMod 13664159) ^ (13664159 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 13664159) ^ ((13664159 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 13664159) ^ ((13664159 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 13664159) ^ ((13664159 - 1) / 401887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13664159 (11 : ZMod 13664159)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (17, 1), (401887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (17, 1), (401887, 1)] : List FactorBlock).map factorBlockValue).prod = 13664159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64ElevenI_401887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_14329009 : Nat.Prime 14329009 := by
  have hfermat : (11 : ZMod 14329009) ^ (14329009 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 14329009) ^ ((14329009 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 14329009) ^ ((14329009 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 14329009) ^ ((14329009 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 14329009) ^ ((14329009 - 1) / 809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14329009 (11 : ZMod 14329009)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (41, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (41, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod = 14329009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_free64ElevenI_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_18466379 : Nat.Prime 18466379 := by
  have hfermat : (2 : ZMod 18466379) ^ (18466379 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 18466379) ^ ((18466379 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 18466379) ^ ((18466379 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 18466379) ^ ((18466379 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 18466379) ^ ((18466379 - 1) / 57349) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18466379 (2 : ZMod 18466379)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (23, 1), (57349, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (23, 1), (57349, 1)] : List FactorBlock).map factorBlockValue).prod = 18466379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_23
      · exact prime_free64ElevenI_57349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_25824109 : Nat.Prime 25824109 := by
  have hfermat : (2 : ZMod 25824109) ^ (25824109 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 25824109) ^ ((25824109 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 25824109) ^ ((25824109 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 25824109) ^ ((25824109 - 1) / 2152009) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 25824109 (2 : ZMod 25824109)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2152009, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2152009, 1)] : List FactorBlock).map factorBlockValue).prod = 25824109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_2152009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_29602789 : Nat.Prime 29602789 := by
  have hfermat : (6 : ZMod 29602789) ^ (29602789 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 29602789) ^ ((29602789 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 29602789) ^ ((29602789 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 29602789) ^ ((29602789 - 1) / 281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 29602789) ^ ((29602789 - 1) / 8779) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 29602789 (6 : ZMod 29602789)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (281, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (281, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod = 29602789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_281
      · exact prime_free64ElevenI_8779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_70846289 : Nat.Prime 70846289 := by
  have hfermat : (3 : ZMod 70846289) ^ (70846289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 70846289) ^ ((70846289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 70846289) ^ ((70846289 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 70846289) ^ ((70846289 - 1) / 241) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 70846289) ^ ((70846289 - 1) / 967) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 70846289 (3 : ZMod 70846289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (19, 1), (241, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (19, 1), (241, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod = 70846289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_241
      · exact prime_free64ElevenI_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_75111599 : Nat.Prime 75111599 := by
  have hfermat : (17 : ZMod 75111599) ^ (75111599 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 75111599) ^ ((75111599 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 75111599) ^ ((75111599 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 75111599) ^ ((75111599 - 1) / 73) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 75111599) ^ ((75111599 - 1) / 27077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 75111599 (17 : ZMod 75111599)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (73, 1), (27077, 1)] : List FactorBlock).map factorBlockValue).prod = 75111599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_t64_73
      · exact prime_free64ElevenI_27077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_79485869 : Nat.Prime 79485869 := by
  have hfermat : (2 : ZMod 79485869) ^ (79485869 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 79485869) ^ ((79485869 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 79485869) ^ ((79485869 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 79485869) ^ ((79485869 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 79485869) ^ ((79485869 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 79485869) ^ ((79485869 - 1) / 809) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 79485869 (2 : ZMod 79485869)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (11, 2), (29, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (11, 2), (29, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod = 79485869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_t64_29
      · exact prime_free64ElevenI_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_103835981 : Nat.Prime 103835981 := by
  have hfermat : (2 : ZMod 103835981) ^ (103835981 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 103835981) ^ ((103835981 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 103835981) ^ ((103835981 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 103835981) ^ ((103835981 - 1) / 5191799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 103835981 (2 : ZMod 103835981)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (5191799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (5191799, 1)] : List FactorBlock).map factorBlockValue).prod = 103835981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_5191799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_174042899 : Nat.Prime 174042899 := by
  have hfermat : (2 : ZMod 174042899) ^ (174042899 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 174042899) ^ ((174042899 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 174042899) ^ ((174042899 - 1) / 251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 174042899) ^ ((174042899 - 1) / 346699) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 174042899 (2 : ZMod 174042899)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (251, 1), (346699, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (251, 1), (346699, 1)] : List FactorBlock).map factorBlockValue).prod = 174042899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_251
      · exact prime_free64ElevenI_346699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_188131817 : Nat.Prime 188131817 := by
  have hfermat : (3 : ZMod 188131817) ^ (188131817 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 188131817) ^ ((188131817 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 188131817) ^ ((188131817 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 188131817) ^ ((188131817 - 1) / 810913) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 188131817 (3 : ZMod 188131817)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (29, 1), (810913, 1)] : List FactorBlock).map factorBlockValue).prod = 188131817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_free64ElevenI_810913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_251922637 : Nat.Prime 251922637 := by
  have hfermat : (2 : ZMod 251922637) ^ (251922637 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 251922637) ^ ((251922637 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 251922637) ^ ((251922637 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 251922637) ^ ((251922637 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 251922637) ^ ((251922637 - 1) / 277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 251922637) ^ ((251922637 - 1) / 401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 251922637 (2 : ZMod 251922637)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 4), (7, 1), (277, 1), (401, 1)] : List FactorBlock).map factorBlockValue).prod = 251922637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64ElevenI_277
      · exact prime_free64ElevenI_401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_289278289 : Nat.Prime 289278289 := by
  have hfermat : (7 : ZMod 289278289) ^ (289278289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 289278289) ^ ((289278289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 289278289) ^ ((289278289 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 289278289) ^ ((289278289 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 289278289) ^ ((289278289 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 289278289) ^ ((289278289 - 1) / 3769) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 289278289 (7 : ZMod 289278289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (13, 1), (41, 1), (3769, 1)] : List FactorBlock).map factorBlockValue).prod = 289278289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_41
      · exact prime_t64_3769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_303537701 : Nat.Prime 303537701 := by
  have hfermat : (2 : ZMod 303537701) ^ (303537701 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 303537701) ^ ((303537701 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 303537701) ^ ((303537701 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 303537701) ^ ((303537701 - 1) / 587) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 303537701) ^ ((303537701 - 1) / 5171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 303537701 (2 : ZMod 303537701)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 2), (587, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 2), (587, 1), (5171, 1)] : List FactorBlock).map factorBlockValue).prod = 303537701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_587
      · exact prime_free64ElevenI_5171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_423992911 : Nat.Prime 423992911 := by
  have hfermat : (11 : ZMod 423992911) ^ (423992911 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 423992911) ^ ((423992911 - 1) / 8623) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 423992911 (11 : ZMod 423992911)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (149, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (149, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod = 423992911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_149
      · exact prime_free64ElevenI_8623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_450713209 : Nat.Prime 450713209 := by
  have hfermat : (17 : ZMod 450713209) ^ (450713209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 450713209) ^ ((450713209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 450713209) ^ ((450713209 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 450713209) ^ ((450713209 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 450713209) ^ ((450713209 - 1) / 593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 450713209) ^ ((450713209 - 1) / 2879) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 450713209 (17 : ZMod 450713209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (593, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (593, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod = 450713209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64ElevenI_593
      · exact prime_free64ElevenI_2879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_465392159 : Nat.Prime 465392159 := by
  have hfermat : (7 : ZMod 465392159) ^ (465392159 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 465392159) ^ ((465392159 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 465392159) ^ ((465392159 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 465392159) ^ ((465392159 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 465392159) ^ ((465392159 - 1) / 3022027) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 465392159 (7 : ZMod 465392159)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (3022027, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (3022027, 1)] : List FactorBlock).map factorBlockValue).prod = 465392159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64ElevenI_3022027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_767926501 : Nat.Prime 767926501 := by
  have hfermat : (2 : ZMod 767926501) ^ (767926501 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 767926501) ^ ((767926501 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 767926501) ^ ((767926501 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 767926501) ^ ((767926501 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 767926501) ^ ((767926501 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 767926501) ^ ((767926501 - 1) / 4231) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 767926501 (2 : ZMod 767926501)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 3), (11, 2), (4231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 3), (11, 2), (4231, 1)] : List FactorBlock).map factorBlockValue).prod = 767926501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64ElevenI_4231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_74144261 : Nat.Prime 74144261 := by
  have hfermat : (2 : ZMod 74144261) ^ (74144261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 74144261) ^ ((74144261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 74144261) ^ ((74144261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 74144261) ^ ((74144261 - 1) / 3707213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 74144261 (2 : ZMod 74144261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (3707213, 1)] : List FactorBlock).map factorBlockValue).prod = 74144261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_3707213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_889731133 : Nat.Prime 889731133 := by
  have hfermat : (2 : ZMod 889731133) ^ (889731133 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 889731133) ^ ((889731133 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 889731133) ^ ((889731133 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 889731133) ^ ((889731133 - 1) / 74144261) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 889731133 (2 : ZMod 889731133)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (74144261, 1)] : List FactorBlock).map factorBlockValue).prod = 889731133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_74144261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_946695979 : Nat.Prime 946695979 := by
  have hfermat : (2 : ZMod 946695979) ^ (946695979 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 946695979) ^ ((946695979 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 946695979) ^ ((946695979 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 946695979) ^ ((946695979 - 1) / 2351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 946695979) ^ ((946695979 - 1) / 7457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 946695979 (2 : ZMod 946695979)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (2351, 1), (7457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (2351, 1), (7457, 1)] : List FactorBlock).map factorBlockValue).prod = 946695979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_2351
      · exact prime_free64ElevenI_7457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_20341261 : Nat.Prime 20341261 := by
  have hfermat : (6 : ZMod 20341261) ^ (20341261 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 20341261) ^ ((20341261 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 20341261) ^ ((20341261 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 20341261) ^ ((20341261 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 20341261) ^ ((20341261 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 20341261) ^ ((20341261 - 1) / 271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 20341261 (6 : ZMod 20341261)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (139, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (139, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod = 20341261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_139
      · exact prime_free64ElevenI_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1057745573 : Nat.Prime 1057745573 := by
  have hfermat : (2 : ZMod 1057745573) ^ (1057745573 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1057745573) ^ ((1057745573 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1057745573) ^ ((1057745573 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1057745573) ^ ((1057745573 - 1) / 20341261) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1057745573 (2 : ZMod 1057745573)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (20341261, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (20341261, 1)] : List FactorBlock).map factorBlockValue).prod = 1057745573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64ElevenI_20341261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1073490031 : Nat.Prime 1073490031 := by
  have hfermat : (3 : ZMod 1073490031) ^ (1073490031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1073490031) ^ ((1073490031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1073490031) ^ ((1073490031 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1073490031) ^ ((1073490031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1073490031) ^ ((1073490031 - 1) / 409) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1073490031) ^ ((1073490031 - 1) / 9721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1073490031 (3 : ZMod 1073490031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (409, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (409, 1), (9721, 1)] : List FactorBlock).map factorBlockValue).prod = 1073490031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_409
      · exact prime_free64ElevenI_9721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1773847591 : Nat.Prime 1773847591 := by
  have hfermat : (3 : ZMod 1773847591) ^ (1773847591 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 1773847591) ^ ((1773847591 - 1) / 6133) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1773847591 (3 : ZMod 1773847591)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (31, 1), (311, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod = 1773847591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_t64_311
      · exact prime_free64ElevenI_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_1842344461 : Nat.Prime 1842344461 := by
  have hfermat : (2 : ZMod 1842344461) ^ (1842344461 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 1842344461) ^ ((1842344461 - 1) / 7213) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1842344461 (2 : ZMod 1842344461)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (11, 1), (43, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (11, 1), (43, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod = 1842344461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_43
      · exact prime_free64ElevenI_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_2064319931 : Nat.Prime 2064319931 := by
  have hfermat : (2 : ZMod 2064319931) ^ (2064319931 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2064319931) ^ ((2064319931 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2064319931) ^ ((2064319931 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2064319931) ^ ((2064319931 - 1) / 401) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2064319931) ^ ((2064319931 - 1) / 514793) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2064319931 (2 : ZMod 2064319931)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (401, 1), (514793, 1)] : List FactorBlock).map factorBlockValue).prod = 2064319931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_401
      · exact prime_free64ElevenI_514793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2779889117 : Nat.Prime 2779889117 := by
  have hfermat : (2 : ZMod 2779889117) ^ (2779889117 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2779889117) ^ ((2779889117 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2779889117) ^ ((2779889117 - 1) / 19553) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2779889117) ^ ((2779889117 - 1) / 35543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2779889117 (2 : ZMod 2779889117)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19553, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19553, 1), (35543, 1)] : List FactorBlock).map factorBlockValue).prod = 2779889117 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_19553
      · exact prime_free64ElevenI_35543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_2848589311 : Nat.Prime 2848589311 := by
  have hfermat : (6 : ZMod 2848589311) ^ (2848589311 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 331) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (6 : ZMod 2848589311) ^ ((2848589311 - 1) / 383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2848589311 (6 : ZMod 2848589311)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (107, 1), (331, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod = 2848589311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_107
      · exact prime_free64ElevenI_331
      · exact prime_t64_383
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

private theorem prime_free64ElevenI_71096953 : Nat.Prime 71096953 := by
  have hfermat : (13 : ZMod 71096953) ^ (71096953 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 71096953) ^ ((71096953 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 71096953) ^ ((71096953 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 71096953) ^ ((71096953 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 71096953) ^ ((71096953 - 1) / 72253) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 71096953 (13 : ZMod 71096953)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (41, 1), (72253, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (41, 1), (72253, 1)] : List FactorBlock).map factorBlockValue).prod = 71096953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_free64ElevenI_72253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2986072027 : Nat.Prime 2986072027 := by
  have hfermat : (2 : ZMod 2986072027) ^ (2986072027 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2986072027) ^ ((2986072027 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2986072027) ^ ((2986072027 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2986072027) ^ ((2986072027 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2986072027) ^ ((2986072027 - 1) / 71096953) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2986072027 (2 : ZMod 2986072027)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (71096953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (71096953, 1)] : List FactorBlock).map factorBlockValue).prod = 2986072027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64ElevenI_71096953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_60308257 : Nat.Prime 60308257 := by
  have hfermat : (5 : ZMod 60308257) ^ (60308257 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 60308257) ^ ((60308257 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 60308257) ^ ((60308257 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 60308257) ^ ((60308257 - 1) / 643) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 60308257) ^ ((60308257 - 1) / 977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 60308257 (5 : ZMod 60308257)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (643, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod = 60308257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_643
      · exact prime_free64ElevenI_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_5789592673 : Nat.Prime 5789592673 := by
  have hfermat : (10 : ZMod 5789592673) ^ (5789592673 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 5789592673) ^ ((5789592673 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 5789592673) ^ ((5789592673 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 5789592673) ^ ((5789592673 - 1) / 60308257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5789592673 (10 : ZMod 5789592673)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (60308257, 1)] : List FactorBlock).map factorBlockValue).prod = 5789592673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_60308257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_7398490091 : Nat.Prime 7398490091 := by
  have hfermat : (2 : ZMod 7398490091) ^ (7398490091 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7398490091) ^ ((7398490091 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7398490091) ^ ((7398490091 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7398490091) ^ ((7398490091 - 1) / 2927) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7398490091) ^ ((7398490091 - 1) / 252767) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7398490091 (2 : ZMod 7398490091)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (2927, 1), (252767, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (2927, 1), (252767, 1)] : List FactorBlock).map factorBlockValue).prod = 7398490091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_2927
      · exact prime_free64ElevenI_252767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_505512671 : Nat.Prime 505512671 := by
  have hfermat : (11 : ZMod 505512671) ^ (505512671 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 505512671) ^ ((505512671 - 1) / 1987) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 505512671 (11 : ZMod 505512671)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (13, 1), (19, 1), (103, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (13, 1), (19, 1), (103, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod = 505512671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_19
      · exact prime_t64_103
      · exact prime_free64ElevenI_1987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_10110253421 : Nat.Prime 10110253421 := by
  have hfermat : (3 : ZMod 10110253421) ^ (10110253421 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 10110253421) ^ ((10110253421 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 10110253421) ^ ((10110253421 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 10110253421) ^ ((10110253421 - 1) / 505512671) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10110253421 (3 : ZMod 10110253421)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (505512671, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (505512671, 1)] : List FactorBlock).map factorBlockValue).prod = 10110253421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_505512671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_13232350871 : Nat.Prime 13232350871 := by
  have hfermat : (11 : ZMod 13232350871) ^ (13232350871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 13232350871) ^ ((13232350871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 13232350871) ^ ((13232350871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 13232350871) ^ ((13232350871 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 13232350871) ^ ((13232350871 - 1) / 2297) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 13232350871) ^ ((13232350871 - 1) / 13397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13232350871 (11 : ZMod 13232350871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (43, 1), (2297, 1), (13397, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (43, 1), (2297, 1), (13397, 1)] : List FactorBlock).map factorBlockValue).prod = 13232350871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_43
      · exact prime_free64ElevenI_2297
      · exact prime_free64ElevenI_13397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_15837208853 : Nat.Prime 15837208853 := by
  have hfermat : (2 : ZMod 15837208853) ^ (15837208853 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15837208853) ^ ((15837208853 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15837208853) ^ ((15837208853 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 15837208853) ^ ((15837208853 - 1) / 9257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 15837208853) ^ ((15837208853 - 1) / 22511) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15837208853 (2 : ZMod 15837208853)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (9257, 1), (22511, 1)] : List FactorBlock).map factorBlockValue).prod = 15837208853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_9257
      · exact prime_free64ElevenI_22511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_36072713069 : Nat.Prime 36072713069 := by
  have hfermat : (2 : ZMod 36072713069) ^ (36072713069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 36072713069) ^ ((36072713069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 36072713069) ^ ((36072713069 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 36072713069) ^ ((36072713069 - 1) / 4679) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 36072713069) ^ ((36072713069 - 1) / 275339) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 36072713069 (2 : ZMod 36072713069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (4679, 1), (275339, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (4679, 1), (275339, 1)] : List FactorBlock).map factorBlockValue).prod = 36072713069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_4679
      · exact prime_free64ElevenI_275339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_19804481 : Nat.Prime 19804481 := by
  have hfermat : (3 : ZMod 19804481) ^ (19804481 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 19804481) ^ ((19804481 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 19804481) ^ ((19804481 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 19804481) ^ ((19804481 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 19804481) ^ ((19804481 - 1) / 311) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19804481 (3 : ZMod 19804481)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (199, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (199, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod = 19804481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_199
      · exact prime_t64_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_118826887 : Nat.Prime 118826887 := by
  have hfermat : (6 : ZMod 118826887) ^ (118826887 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 118826887) ^ ((118826887 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 118826887) ^ ((118826887 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 118826887) ^ ((118826887 - 1) / 19804481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 118826887 (6 : ZMod 118826887)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19804481, 1)] : List FactorBlock).map factorBlockValue).prod = 118826887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_19804481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_18299340599 : Nat.Prime 18299340599 := by
  have hfermat : (7 : ZMod 18299340599) ^ (18299340599 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 18299340599) ^ ((18299340599 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 18299340599) ^ ((18299340599 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 18299340599) ^ ((18299340599 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 18299340599) ^ ((18299340599 - 1) / 118826887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18299340599 (7 : ZMod 18299340599)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (11, 1), (118826887, 1)] : List FactorBlock).map factorBlockValue).prod = 18299340599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64ElevenI_118826887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_36598681199 : Nat.Prime 36598681199 := by
  have hfermat : (11 : ZMod 36598681199) ^ (36598681199 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 36598681199) ^ ((36598681199 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 36598681199) ^ ((36598681199 - 1) / 18299340599) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 36598681199 (11 : ZMod 36598681199)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (18299340599, 1)] : List FactorBlock).map factorBlockValue).prod = 36598681199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_18299340599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_36966987433 : Nat.Prime 36966987433 := by
  have hfermat : (5 : ZMod 36966987433) ^ (36966987433 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 36966987433) ^ ((36966987433 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 36966987433) ^ ((36966987433 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 36966987433) ^ ((36966987433 - 1) / 353) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 36966987433) ^ ((36966987433 - 1) / 1454477) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 36966987433 (5 : ZMod 36966987433)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (353, 1), (1454477, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (353, 1), (1454477, 1)] : List FactorBlock).map factorBlockValue).prod = 36966987433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_353
      · exact prime_free64ElevenI_1454477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_56990814479 : Nat.Prime 56990814479 := by
  have hfermat : (7 : ZMod 56990814479) ^ (56990814479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 56990814479) ^ ((56990814479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 56990814479) ^ ((56990814479 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 56990814479) ^ ((56990814479 - 1) / 827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 56990814479) ^ ((56990814479 - 1) / 1039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 56990814479) ^ ((56990814479 - 1) / 2551) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 56990814479 (7 : ZMod 56990814479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (827, 1), (1039, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (827, 1), (1039, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod = 56990814479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64ElevenI_827
      · exact prime_free64ElevenI_1039
      · exact prime_free64ElevenI_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_19773451 : Nat.Prime 19773451 := by
  have hfermat : (3 : ZMod 19773451) ^ (19773451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 19773451) ^ ((19773451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 19773451) ^ ((19773451 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 19773451) ^ ((19773451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 19773451) ^ ((19773451 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 19773451) ^ ((19773451 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19773451 (3 : ZMod 19773451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (97, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (97, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod = 19773451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_97
      · exact prime_free64ElevenI_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_435015923 : Nat.Prime 435015923 := by
  have hfermat : (2 : ZMod 435015923) ^ (435015923 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 435015923) ^ ((435015923 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 435015923) ^ ((435015923 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 435015923) ^ ((435015923 - 1) / 19773451) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 435015923 (2 : ZMod 435015923)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (19773451, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (19773451, 1)] : List FactorBlock).map factorBlockValue).prod = 435015923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64ElevenI_19773451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_65252388451 : Nat.Prime 65252388451 := by
  have hfermat : (2 : ZMod 65252388451) ^ (65252388451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 65252388451) ^ ((65252388451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 65252388451) ^ ((65252388451 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 65252388451) ^ ((65252388451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 65252388451) ^ ((65252388451 - 1) / 435015923) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 65252388451 (2 : ZMod 65252388451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (435015923, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (435015923, 1)] : List FactorBlock).map factorBlockValue).prod = 65252388451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_435015923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_39971971421 : Nat.Prime 39971971421 := by
  have hfermat : (2 : ZMod 39971971421) ^ (39971971421 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 503) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 39971971421) ^ ((39971971421 - 1) / 1229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 39971971421 (2 : ZMod 39971971421)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (53, 1), (61, 1), (503, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (53, 1), (61, 1), (503, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod = 39971971421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_t64_61
      · exact prime_free64ElevenI_503
      · exact prime_t64_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_79943942843 : Nat.Prime 79943942843 := by
  have hfermat : (2 : ZMod 79943942843) ^ (79943942843 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 79943942843) ^ ((79943942843 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 79943942843) ^ ((79943942843 - 1) / 39971971421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 79943942843 (2 : ZMod 79943942843)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (39971971421, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (39971971421, 1)] : List FactorBlock).map factorBlockValue).prod = 79943942843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_39971971421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_963143029 : Nat.Prime 963143029 := by
  have hfermat : (2 : ZMod 963143029) ^ (963143029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 963143029) ^ ((963143029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 963143029) ^ ((963143029 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 963143029) ^ ((963143029 - 1) / 8917991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 963143029 (2 : ZMod 963143029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (8917991, 1)] : List FactorBlock).map factorBlockValue).prod = 963143029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_8917991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_84756586553 : Nat.Prime 84756586553 := by
  have hfermat : (3 : ZMod 84756586553) ^ (84756586553 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 84756586553) ^ ((84756586553 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 84756586553) ^ ((84756586553 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 84756586553) ^ ((84756586553 - 1) / 963143029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 84756586553 (3 : ZMod 84756586553)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (963143029, 1)] : List FactorBlock).map factorBlockValue).prod = 84756586553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64ElevenI_963143029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_151858876903 : Nat.Prime 151858876903 := by
  have hfermat : (3 : ZMod 151858876903) ^ (151858876903 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 151858876903) ^ ((151858876903 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 151858876903) ^ ((151858876903 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 151858876903) ^ ((151858876903 - 1) / 3793) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 151858876903) ^ ((151858876903 - 1) / 6672769) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 151858876903 (3 : ZMod 151858876903)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (3793, 1), (6672769, 1)] : List FactorBlock).map factorBlockValue).prod = 151858876903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_3793
      · exact prime_free64ElevenI_6672769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_19148383 : Nat.Prime 19148383 := by
  have hfermat : (5 : ZMod 19148383) ^ (19148383 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 19148383) ^ ((19148383 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 19148383) ^ ((19148383 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 19148383) ^ ((19148383 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 19148383) ^ ((19148383 - 1) / 97) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 19148383) ^ ((19148383 - 1) / 997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19148383 (5 : ZMod 19148383)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (97, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (97, 1), (997, 1)] : List FactorBlock).map factorBlockValue).prod = 19148383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_97
      · exact prime_t64_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_175092814153 : Nat.Prime 175092814153 := by
  have hfermat : (5 : ZMod 175092814153) ^ (175092814153 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 175092814153) ^ ((175092814153 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 175092814153) ^ ((175092814153 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 175092814153) ^ ((175092814153 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 175092814153) ^ ((175092814153 - 1) / 19148383) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 175092814153 (5 : ZMod 175092814153)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (127, 1), (19148383, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (127, 1), (19148383, 1)] : List FactorBlock).map factorBlockValue).prod = 175092814153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_127
      · exact prime_free64ElevenI_19148383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_23981183 : Nat.Prime 23981183 := by
  have hfermat : (5 : ZMod 23981183) ^ (23981183 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 23981183) ^ ((23981183 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 23981183) ^ ((23981183 - 1) / 397) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 23981183) ^ ((23981183 - 1) / 30203) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 23981183 (5 : ZMod 23981183)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (397, 1), (30203, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (397, 1), (30203, 1)] : List FactorBlock).map factorBlockValue).prod = 23981183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_397
      · exact prime_free64ElevenI_30203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_32422559417 : Nat.Prime 32422559417 := by
  have hfermat : (3 : ZMod 32422559417) ^ (32422559417 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 32422559417) ^ ((32422559417 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 32422559417) ^ ((32422559417 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 32422559417) ^ ((32422559417 - 1) / 23981183) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 32422559417 (3 : ZMod 32422559417)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (13, 2), (23981183, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (13, 2), (23981183, 1)] : List FactorBlock).map factorBlockValue).prod = 32422559417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64ElevenI_23981183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_194535356503 : Nat.Prime 194535356503 := by
  have hfermat : (5 : ZMod 194535356503) ^ (194535356503 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 194535356503) ^ ((194535356503 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 194535356503) ^ ((194535356503 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 194535356503) ^ ((194535356503 - 1) / 32422559417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 194535356503 (5 : ZMod 194535356503)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32422559417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32422559417, 1)] : List FactorBlock).map factorBlockValue).prod = 194535356503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_32422559417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_4298439403 : Nat.Prime 4298439403 := by
  have hfermat : (2 : ZMod 4298439403) ^ (4298439403 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4298439403) ^ ((4298439403 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4298439403) ^ ((4298439403 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4298439403) ^ ((4298439403 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 4298439403) ^ ((4298439403 - 1) / 719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 4298439403) ^ ((4298439403 - 1) / 1669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4298439403 (2 : ZMod 4298439403)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (199, 1), (719, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (199, 1), (719, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod = 4298439403 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_199
      · exact prime_t64_719
      · exact prime_t64_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_223518848957 : Nat.Prime 223518848957 := by
  have hfermat : (2 : ZMod 223518848957) ^ (223518848957 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 223518848957) ^ ((223518848957 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 223518848957) ^ ((223518848957 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 223518848957) ^ ((223518848957 - 1) / 4298439403) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 223518848957 (2 : ZMod 223518848957)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (13, 1), (4298439403, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (13, 1), (4298439403, 1)] : List FactorBlock).map factorBlockValue).prod = 223518848957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_free64ElevenI_4298439403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_127435031 : Nat.Prime 127435031 := by
  have hfermat : (11 : ZMod 127435031) ^ (127435031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 127435031) ^ ((127435031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 127435031) ^ ((127435031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 127435031) ^ ((127435031 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 127435031) ^ ((127435031 - 1) / 163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 127435031) ^ ((127435031 - 1) / 2113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 127435031 (11 : ZMod 127435031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37, 1), (163, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod = 127435031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_37
      · exact prime_t64_163
      · exact prime_free64ElevenI_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_252321361381 : Nat.Prime 252321361381 := by
  have hfermat : (2 : ZMod 252321361381) ^ (252321361381 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 252321361381) ^ ((252321361381 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 252321361381) ^ ((252321361381 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 252321361381) ^ ((252321361381 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 252321361381) ^ ((252321361381 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 252321361381) ^ ((252321361381 - 1) / 127435031) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 252321361381 (2 : ZMod 252321361381)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (11, 1), (127435031, 1)] : List FactorBlock).map factorBlockValue).prod = 252321361381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64ElevenI_127435031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_15245267 : Nat.Prime 15245267 := by
  have hfermat : (2 : ZMod 15245267) ^ (15245267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 15245267) ^ ((15245267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 15245267) ^ ((15245267 - 1) / 7622633) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 15245267 (2 : ZMod 15245267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7622633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7622633, 1)] : List FactorBlock).map factorBlockValue).prod = 15245267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_7622633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_1483059573761 : Nat.Prime 1483059573761 := by
  have hfermat : (3 : ZMod 1483059573761) ^ (1483059573761 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1483059573761) ^ ((1483059573761 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1483059573761) ^ ((1483059573761 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1483059573761) ^ ((1483059573761 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1483059573761) ^ ((1483059573761 - 1) / 15245267) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1483059573761 (3 : ZMod 1483059573761)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 10), (5, 1), (19, 1), (15245267, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 10), (5, 1), (19, 1), (15245267, 1)] : List FactorBlock).map factorBlockValue).prod = 1483059573761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_free64ElevenI_15245267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1754527902319 : Nat.Prime 1754527902319 := by
  have hfermat : (3 : ZMod 1754527902319) ^ (1754527902319 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1754527902319) ^ ((1754527902319 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1754527902319) ^ ((1754527902319 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1754527902319) ^ ((1754527902319 - 1) / 719) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1754527902319) ^ ((1754527902319 - 1) / 2819) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1754527902319) ^ ((1754527902319 - 1) / 48091) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1754527902319 (3 : ZMod 1754527902319)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (719, 1), (2819, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (719, 1), (2819, 1), (48091, 1)] : List FactorBlock).map factorBlockValue).prod = 1754527902319 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_719
      · exact prime_free64ElevenI_2819
      · exact prime_free64ElevenI_48091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_761425369 : Nat.Prime 761425369 := by
  have hfermat : (7 : ZMod 761425369) ^ (761425369 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 761425369) ^ ((761425369 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 761425369) ^ ((761425369 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 761425369) ^ ((761425369 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 761425369) ^ ((761425369 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 761425369) ^ ((761425369 - 1) / 77951) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 761425369 (7 : ZMod 761425369)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (37, 1), (77951, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (37, 1), (77951, 1)] : List FactorBlock).map factorBlockValue).prod = 761425369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_37
      · exact prime_free64ElevenI_77951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_3365500130981 : Nat.Prime 3365500130981 := by
  have hfermat : (2 : ZMod 3365500130981) ^ (3365500130981 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3365500130981) ^ ((3365500130981 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3365500130981) ^ ((3365500130981 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3365500130981) ^ ((3365500130981 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 3365500130981) ^ ((3365500130981 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 3365500130981) ^ ((3365500130981 - 1) / 761425369) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3365500130981 (2 : ZMod 3365500130981)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (13, 1), (17, 1), (761425369, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (13, 1), (17, 1), (761425369, 1)] : List FactorBlock).map factorBlockValue).prod = 3365500130981 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_17
      · exact prime_free64ElevenI_761425369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_804002329211 : Nat.Prime 804002329211 := by
  have hfermat : (2 : ZMod 804002329211) ^ (804002329211 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 804002329211) ^ ((804002329211 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 804002329211) ^ ((804002329211 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 804002329211) ^ ((804002329211 - 1) / 37579) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 804002329211) ^ ((804002329211 - 1) / 2139499) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 804002329211 (2 : ZMod 804002329211)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (37579, 1), (2139499, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (37579, 1), (2139499, 1)] : List FactorBlock).map factorBlockValue).prod = 804002329211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_37579
      · exact prime_free64ElevenI_2139499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_4824013975267 : Nat.Prime 4824013975267 := by
  have hfermat : (2 : ZMod 4824013975267) ^ (4824013975267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 4824013975267) ^ ((4824013975267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 4824013975267) ^ ((4824013975267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 4824013975267) ^ ((4824013975267 - 1) / 804002329211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4824013975267 (2 : ZMod 4824013975267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (804002329211, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (804002329211, 1)] : List FactorBlock).map factorBlockValue).prod = 4824013975267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_804002329211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_7220933861803 : Nat.Prime 7220933861803 := by
  have hfermat : (2 : ZMod 7220933861803) ^ (7220933861803 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 7220933861803) ^ ((7220933861803 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 7220933861803) ^ ((7220933861803 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 7220933861803) ^ ((7220933861803 - 1) / 1109) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 7220933861803) ^ ((7220933861803 - 1) / 2011) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 7220933861803) ^ ((7220933861803 - 1) / 539633) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7220933861803 (2 : ZMod 7220933861803)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1109, 1), (2011, 1), (539633, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1109, 1), (2011, 1), (539633, 1)] : List FactorBlock).map factorBlockValue).prod = 7220933861803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_1109
      · exact prime_free64ElevenI_2011
      · exact prime_free64ElevenI_539633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_11163319554953 : Nat.Prime 11163319554953 := by
  have hfermat : (3 : ZMod 11163319554953) ^ (11163319554953 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11163319554953) ^ ((11163319554953 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11163319554953) ^ ((11163319554953 - 1) / 127) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11163319554953) ^ ((11163319554953 - 1) / 12049) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11163319554953) ^ ((11163319554953 - 1) / 911903) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11163319554953 (3 : ZMod 11163319554953)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (127, 1), (12049, 1), (911903, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (127, 1), (12049, 1), (911903, 1)] : List FactorBlock).map factorBlockValue).prod = 11163319554953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_127
      · exact prime_free64ElevenI_12049
      · exact prime_free64ElevenI_911903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_45595501013 : Nat.Prime 45595501013 := by
  have hfermat : (2 : ZMod 45595501013) ^ (45595501013 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 45595501013) ^ ((45595501013 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 45595501013) ^ ((45595501013 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 45595501013) ^ ((45595501013 - 1) / 263) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 45595501013) ^ ((45595501013 - 1) / 316363) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 45595501013 (2 : ZMod 45595501013)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (137, 1), (263, 1), (316363, 1)] : List FactorBlock).map factorBlockValue).prod = 45595501013 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_137
      · exact prime_t64_263
      · exact prime_free64ElevenI_316363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_17782245395071 : Nat.Prime 17782245395071 := by
  have hfermat : (6 : ZMod 17782245395071) ^ (17782245395071 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 17782245395071) ^ ((17782245395071 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 17782245395071) ^ ((17782245395071 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 17782245395071) ^ ((17782245395071 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 17782245395071) ^ ((17782245395071 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 17782245395071) ^ ((17782245395071 - 1) / 45595501013) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17782245395071 (6 : ZMod 17782245395071)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (45595501013, 1)] : List FactorBlock).map factorBlockValue).prod = 17782245395071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64ElevenI_45595501013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_2582040281 : Nat.Prime 2582040281 := by
  have hfermat : (3 : ZMod 2582040281) ^ (2582040281 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2582040281) ^ ((2582040281 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2582040281) ^ ((2582040281 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2582040281) ^ ((2582040281 - 1) / 373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2582040281) ^ ((2582040281 - 1) / 173059) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2582040281 (3 : ZMod 2582040281)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (373, 1), (173059, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (373, 1), (173059, 1)] : List FactorBlock).map factorBlockValue).prod = 2582040281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_373
      · exact prime_free64ElevenI_173059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_32146401498451 : Nat.Prime 32146401498451 := by
  have hfermat : (2 : ZMod 32146401498451) ^ (32146401498451 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 32146401498451) ^ ((32146401498451 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 32146401498451) ^ ((32146401498451 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 32146401498451) ^ ((32146401498451 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 32146401498451) ^ ((32146401498451 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 32146401498451) ^ ((32146401498451 - 1) / 2582040281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 32146401498451 (2 : ZMod 32146401498451)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 2), (83, 1), (2582040281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 2), (83, 1), (2582040281, 1)] : List FactorBlock).map factorBlockValue).prod = 32146401498451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_83
      · exact prime_free64ElevenI_2582040281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_406823101 : Nat.Prime 406823101 := by
  have hfermat : (10 : ZMod 406823101) ^ (406823101 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 406823101) ^ ((406823101 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 406823101) ^ ((406823101 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 406823101) ^ ((406823101 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 406823101) ^ ((406823101 - 1) / 1356077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 406823101 (10 : ZMod 406823101)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 2), (1356077, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 2), (1356077, 1)] : List FactorBlock).map factorBlockValue).prod = 406823101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_1356077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_39737666859479 : Nat.Prime 39737666859479 := by
  have hfermat : (7 : ZMod 39737666859479) ^ (39737666859479 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 39737666859479) ^ ((39737666859479 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 39737666859479) ^ ((39737666859479 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 39737666859479) ^ ((39737666859479 - 1) / 6977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 39737666859479) ^ ((39737666859479 - 1) / 406823101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 39737666859479 (7 : ZMod 39737666859479)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (6977, 1), (406823101, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (6977, 1), (406823101, 1)] : List FactorBlock).map factorBlockValue).prod = 39737666859479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_6977
      · exact prime_free64ElevenI_406823101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_930509509 : Nat.Prime 930509509 := by
  have hfermat : (6 : ZMod 930509509) ^ (930509509 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 930509509) ^ ((930509509 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 930509509) ^ ((930509509 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 930509509) ^ ((930509509 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 930509509) ^ ((930509509 - 1) / 593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 930509509) ^ ((930509509 - 1) / 3041) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 930509509 (6 : ZMod 930509509)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (43, 1), (593, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (43, 1), (593, 1), (3041, 1)] : List FactorBlock).map factorBlockValue).prod = 930509509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_free64ElevenI_593
      · exact prime_free64ElevenI_3041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_52986933480497 : Nat.Prime 52986933480497 := by
  have hfermat : (3 : ZMod 52986933480497) ^ (52986933480497 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 52986933480497) ^ ((52986933480497 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 52986933480497) ^ ((52986933480497 - 1) / 3559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 52986933480497) ^ ((52986933480497 - 1) / 930509509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 52986933480497 (3 : ZMod 52986933480497)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3559, 1), (930509509, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3559, 1), (930509509, 1)] : List FactorBlock).map factorBlockValue).prod = 52986933480497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_3559
      · exact prime_free64ElevenI_930509509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1463086601 : Nat.Prime 1463086601 := by
  have hfermat : (3 : ZMod 1463086601) ^ (1463086601 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1463086601) ^ ((1463086601 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1463086601) ^ ((1463086601 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1463086601) ^ ((1463086601 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1463086601) ^ ((1463086601 - 1) / 55843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1463086601 (3 : ZMod 1463086601)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 2), (131, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 2), (131, 1), (55843, 1)] : List FactorBlock).map factorBlockValue).prod = 1463086601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_131
      · exact prime_free64ElevenI_55843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_57955786438813 : Nat.Prime 57955786438813 := by
  have hfermat : (2 : ZMod 57955786438813) ^ (57955786438813 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 57955786438813) ^ ((57955786438813 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 57955786438813) ^ ((57955786438813 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 57955786438813) ^ ((57955786438813 - 1) / 3301) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 57955786438813) ^ ((57955786438813 - 1) / 1463086601) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 57955786438813 (2 : ZMod 57955786438813)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (3301, 1), (1463086601, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (3301, 1), (1463086601, 1)] : List FactorBlock).map factorBlockValue).prod = 57955786438813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_3301
      · exact prime_free64ElevenI_1463086601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_796193727281 : Nat.Prime 796193727281 := by
  have hfermat : (3 : ZMod 796193727281) ^ (796193727281 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 796193727281) ^ ((796193727281 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 796193727281) ^ ((796193727281 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 796193727281) ^ ((796193727281 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 796193727281) ^ ((796193727281 - 1) / 6427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 796193727281) ^ ((796193727281 - 1) / 221219) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 796193727281 (3 : ZMod 796193727281)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (6427, 1), (221219, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (6427, 1), (221219, 1)] : List FactorBlock).map factorBlockValue).prod = 796193727281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64ElevenI_6427
      · exact prime_free64ElevenI_221219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_143314870910581 : Nat.Prime 143314870910581 := by
  have hfermat : (7 : ZMod 143314870910581) ^ (143314870910581 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 143314870910581) ^ ((143314870910581 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 143314870910581) ^ ((143314870910581 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 143314870910581) ^ ((143314870910581 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 143314870910581) ^ ((143314870910581 - 1) / 796193727281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 143314870910581 (7 : ZMod 143314870910581)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (796193727281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (796193727281, 1)] : List FactorBlock).map factorBlockValue).prod = 143314870910581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_796193727281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_61649540501 : Nat.Prime 61649540501 := by
  have hfermat : (2 : ZMod 61649540501) ^ (61649540501 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 61649540501) ^ ((61649540501 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 61649540501) ^ ((61649540501 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 61649540501) ^ ((61649540501 - 1) / 6563) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 61649540501) ^ ((61649540501 - 1) / 18787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 61649540501 (2 : ZMod 61649540501)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 3), (6563, 1), (18787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 3), (6563, 1), (18787, 1)] : List FactorBlock).map factorBlockValue).prod = 61649540501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_6563
      · exact prime_free64ElevenI_18787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2959177944049 : Nat.Prime 2959177944049 := by
  have hfermat : (7 : ZMod 2959177944049) ^ (2959177944049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 2959177944049) ^ ((2959177944049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 2959177944049) ^ ((2959177944049 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 2959177944049) ^ ((2959177944049 - 1) / 61649540501) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2959177944049 (7 : ZMod 2959177944049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (61649540501, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (61649540501, 1)] : List FactorBlock).map factorBlockValue).prod = 2959177944049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_61649540501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_319591217957293 : Nat.Prime 319591217957293 := by
  have hfermat : (2 : ZMod 319591217957293) ^ (319591217957293 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 319591217957293) ^ ((319591217957293 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 319591217957293) ^ ((319591217957293 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 319591217957293) ^ ((319591217957293 - 1) / 2959177944049) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 319591217957293 (2 : ZMod 319591217957293)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (2959177944049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (2959177944049, 1)] : List FactorBlock).map factorBlockValue).prod = 319591217957293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_2959177944049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_68164727 : Nat.Prime 68164727 := by
  have hfermat : (5 : ZMod 68164727) ^ (68164727 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 68164727) ^ ((68164727 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 68164727) ^ ((68164727 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 68164727) ^ ((68164727 - 1) / 4868909) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 68164727 (5 : ZMod 68164727)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (4868909, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (4868909, 1)] : List FactorBlock).map factorBlockValue).prod = 68164727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_4868909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_10770026867 : Nat.Prime 10770026867 := by
  have hfermat : (2 : ZMod 10770026867) ^ (10770026867 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 10770026867) ^ ((10770026867 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 10770026867) ^ ((10770026867 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 10770026867) ^ ((10770026867 - 1) / 68164727) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10770026867 (2 : ZMod 10770026867)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (79, 1), (68164727, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (79, 1), (68164727, 1)] : List FactorBlock).map factorBlockValue).prod = 10770026867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_79
      · exact prime_free64ElevenI_68164727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_385610041946069 : Nat.Prime 385610041946069 := by
  have hfermat : (2 : ZMod 385610041946069) ^ (385610041946069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 385610041946069) ^ ((385610041946069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 385610041946069) ^ ((385610041946069 - 1) / 8951) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 385610041946069) ^ ((385610041946069 - 1) / 10770026867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 385610041946069 (2 : ZMod 385610041946069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (8951, 1), (10770026867, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (8951, 1), (10770026867, 1)] : List FactorBlock).map factorBlockValue).prod = 385610041946069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_8951
      · exact prime_free64ElevenI_10770026867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_433030813401061 : Nat.Prime 433030813401061 := by
  have hfermat : (2 : ZMod 433030813401061) ^ (433030813401061 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 71) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 4937) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (2 : ZMod 433030813401061) ^ ((433030813401061 - 1) / 16073) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 433030813401061 (2 : ZMod 433030813401061)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (5, 1), (7, 1), (61, 1), (71, 1), (4937, 1), (16073, 1)] : List FactorBlock).map factorBlockValue).prod = 433030813401061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_61
      · exact prime_t64_71
      · exact prime_free64ElevenI_4937
      · exact prime_free64ElevenI_16073
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

private theorem prime_free64ElevenI_5954625247 : Nat.Prime 5954625247 := by
  have hfermat : (3 : ZMod 5954625247) ^ (5954625247 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 5954625247) ^ ((5954625247 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 5954625247) ^ ((5954625247 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 5954625247) ^ ((5954625247 - 1) / 1543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 5954625247) ^ ((5954625247 - 1) / 643187) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5954625247 (3 : ZMod 5954625247)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (1543, 1), (643187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (1543, 1), (643187, 1)] : List FactorBlock).map factorBlockValue).prod = 5954625247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_1543
      · exact prime_free64ElevenI_643187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1607748816691 : Nat.Prime 1607748816691 := by
  have hfermat : (2 : ZMod 1607748816691) ^ (1607748816691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1607748816691) ^ ((1607748816691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1607748816691) ^ ((1607748816691 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1607748816691) ^ ((1607748816691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1607748816691) ^ ((1607748816691 - 1) / 5954625247) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1607748816691 (2 : ZMod 1607748816691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (5954625247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (5954625247, 1)] : List FactorBlock).map factorBlockValue).prod = 1607748816691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_5954625247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_434092180506571 : Nat.Prime 434092180506571 := by
  have hfermat : (2 : ZMod 434092180506571) ^ (434092180506571 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 434092180506571) ^ ((434092180506571 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 434092180506571) ^ ((434092180506571 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 434092180506571) ^ ((434092180506571 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 434092180506571) ^ ((434092180506571 - 1) / 1607748816691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 434092180506571 (2 : ZMod 434092180506571)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 1), (1607748816691, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 1), (1607748816691, 1)] : List FactorBlock).map factorBlockValue).prod = 434092180506571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_1607748816691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_5568520721 : Nat.Prime 5568520721 := by
  have hfermat : (6 : ZMod 5568520721) ^ (5568520721 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 5568520721) ^ ((5568520721 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 5568520721) ^ ((5568520721 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 5568520721) ^ ((5568520721 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 5568520721) ^ ((5568520721 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 5568520721) ^ ((5568520721 - 1) / 38393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5568520721 (6 : ZMod 5568520721)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 2), (37, 1), (38393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 2), (37, 1), (38393, 1)] : List FactorBlock).map factorBlockValue).prod = 5568520721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_free64ElevenI_38393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_654590747794993 : Nat.Prime 654590747794993 := by
  have hfermat : (5 : ZMod 654590747794993) ^ (654590747794993 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 654590747794993) ^ ((654590747794993 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 654590747794993) ^ ((654590747794993 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 654590747794993) ^ ((654590747794993 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 654590747794993) ^ ((654590747794993 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 654590747794993) ^ ((654590747794993 - 1) / 5568520721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 654590747794993 (5 : ZMod 654590747794993)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (31, 1), (79, 1), (5568520721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (31, 1), (79, 1), (5568520721, 1)] : List FactorBlock).map factorBlockValue).prod = 654590747794993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_79
      · exact prime_free64ElevenI_5568520721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_988642159474447 : Nat.Prime 988642159474447 := by
  have hfermat : (3 : ZMod 988642159474447) ^ (988642159474447 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 988642159474447) ^ ((988642159474447 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 988642159474447) ^ ((988642159474447 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 988642159474447) ^ ((988642159474447 - 1) / 5869) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 988642159474447) ^ ((988642159474447 - 1) / 8669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 988642159474447) ^ ((988642159474447 - 1) / 1079527) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 988642159474447 (3 : ZMod 988642159474447)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5869, 1), (8669, 1), (1079527, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5869, 1), (8669, 1), (1079527, 1)] : List FactorBlock).map factorBlockValue).prod = 988642159474447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_5869
      · exact prime_free64ElevenI_8669
      · exact prime_free64ElevenI_1079527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_48591551 : Nat.Prime 48591551 := by
  have hfermat : (7 : ZMod 48591551) ^ (48591551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 48591551) ^ ((48591551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 48591551) ^ ((48591551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 48591551) ^ ((48591551 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 48591551) ^ ((48591551 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 48591551) ^ ((48591551 - 1) / 7307) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 48591551 (7 : ZMod 48591551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 2), (7, 1), (19, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 2), (7, 1), (19, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod = 48591551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_free64ElevenI_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1005579309916031 : Nat.Prime 1005579309916031 := by
  have hfermat : (11 : ZMod 1005579309916031) ^ (1005579309916031 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 1005579309916031) ^ ((1005579309916031 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 1005579309916031) ^ ((1005579309916031 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 1005579309916031) ^ ((1005579309916031 - 1) / 569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 1005579309916031) ^ ((1005579309916031 - 1) / 3637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 1005579309916031) ^ ((1005579309916031 - 1) / 48591551) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1005579309916031 (11 : ZMod 1005579309916031)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (569, 1), (3637, 1), (48591551, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (569, 1), (3637, 1), (48591551, 1)] : List FactorBlock).map factorBlockValue).prod = 1005579309916031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_569
      · exact prime_free64ElevenI_3637
      · exact prime_free64ElevenI_48591551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_134406001 : Nat.Prime 134406001 := by
  have hfermat : (17 : ZMod 134406001) ^ (134406001 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 134406001) ^ ((134406001 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 134406001) ^ ((134406001 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 134406001) ^ ((134406001 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 134406001) ^ ((134406001 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (17 : ZMod 134406001) ^ ((134406001 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 134406001 (17 : ZMod 134406001)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 3), (5, 3), (19, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod = 134406001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_19
      · exact prime_free64ElevenI_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1012564812501629 : Nat.Prime 1012564812501629 := by
  have hfermat : (2 : ZMod 1012564812501629) ^ (1012564812501629 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1012564812501629) ^ ((1012564812501629 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1012564812501629) ^ ((1012564812501629 - 1) / 1883407) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1012564812501629) ^ ((1012564812501629 - 1) / 134406001) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1012564812501629 (2 : ZMod 1012564812501629)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (1883407, 1), (134406001, 1)] : List FactorBlock).map factorBlockValue).prod = 1012564812501629 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_1883407
      · exact prime_free64ElevenI_134406001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_11339536811 : Nat.Prime 11339536811 := by
  have hfermat : (6 : ZMod 11339536811) ^ (11339536811 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 11339536811) ^ ((11339536811 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 11339536811) ^ ((11339536811 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 11339536811) ^ ((11339536811 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 11339536811) ^ ((11339536811 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 11339536811) ^ ((11339536811 - 1) / 5225593) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11339536811 (6 : ZMod 11339536811)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (31, 1), (5225593, 1)] : List FactorBlock).map factorBlockValue).prod = 11339536811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_free64ElevenI_5225593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_362865177953 : Nat.Prime 362865177953 := by
  have hfermat : (3 : ZMod 362865177953) ^ (362865177953 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 362865177953) ^ ((362865177953 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 362865177953) ^ ((362865177953 - 1) / 11339536811) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 362865177953 (3 : ZMod 362865177953)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (11339536811, 1)] : List FactorBlock).map factorBlockValue).prod = 362865177953 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_11339536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_1132865085569267 : Nat.Prime 1132865085569267 := by
  have hfermat : (2 : ZMod 1132865085569267) ^ (1132865085569267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1132865085569267) ^ ((1132865085569267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1132865085569267) ^ ((1132865085569267 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1132865085569267) ^ ((1132865085569267 - 1) / 223) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1132865085569267) ^ ((1132865085569267 - 1) / 362865177953) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1132865085569267 (2 : ZMod 1132865085569267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (223, 1), (362865177953, 1)] : List FactorBlock).map factorBlockValue).prod = 1132865085569267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_223
      · exact prime_free64ElevenI_362865177953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_14681717 : Nat.Prime 14681717 := by
  have hfermat : (2 : ZMod 14681717) ^ (14681717 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 14681717) ^ ((14681717 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 14681717) ^ ((14681717 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 14681717) ^ ((14681717 - 1) / 524347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14681717 (2 : ZMod 14681717)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (524347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (524347, 1)] : List FactorBlock).map factorBlockValue).prod = 14681717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_524347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_21846394897 : Nat.Prime 21846394897 := by
  have hfermat : (5 : ZMod 21846394897) ^ (21846394897 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 21846394897) ^ ((21846394897 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 21846394897) ^ ((21846394897 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 21846394897) ^ ((21846394897 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 21846394897) ^ ((21846394897 - 1) / 14681717) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21846394897 (5 : ZMod 21846394897)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (31, 1), (14681717, 1)] : List FactorBlock).map factorBlockValue).prod = 21846394897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_free64ElevenI_14681717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_12146595562733 : Nat.Prime 12146595562733 := by
  have hfermat : (2 : ZMod 12146595562733) ^ (12146595562733 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12146595562733) ^ ((12146595562733 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12146595562733) ^ ((12146595562733 - 1) / 139) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12146595562733) ^ ((12146595562733 - 1) / 21846394897) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12146595562733 (2 : ZMod 12146595562733)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (139, 1), (21846394897, 1)] : List FactorBlock).map factorBlockValue).prod = 12146595562733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_139
      · exact prime_free64ElevenI_21846394897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1384711894151563 : Nat.Prime 1384711894151563 := by
  have hfermat : (2 : ZMod 1384711894151563) ^ (1384711894151563 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1384711894151563) ^ ((1384711894151563 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1384711894151563) ^ ((1384711894151563 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1384711894151563) ^ ((1384711894151563 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1384711894151563) ^ ((1384711894151563 - 1) / 12146595562733) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1384711894151563 (2 : ZMod 1384711894151563)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (19, 1), (12146595562733, 1)] : List FactorBlock).map factorBlockValue).prod = 1384711894151563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_19
      · exact prime_free64ElevenI_12146595562733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2695874388384467 : Nat.Prime 2695874388384467 := by
  have hfermat : (2 : ZMod 2695874388384467) ^ (2695874388384467 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2695874388384467) ^ ((2695874388384467 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2695874388384467) ^ ((2695874388384467 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2695874388384467) ^ ((2695874388384467 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2695874388384467) ^ ((2695874388384467 - 1) / 83459) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2695874388384467) ^ ((2695874388384467 - 1) / 5853893) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2695874388384467 (2 : ZMod 2695874388384467)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (31, 1), (89, 1), (83459, 1), (5853893, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (31, 1), (89, 1), (83459, 1), (5853893, 1)] : List FactorBlock).map factorBlockValue).prod = 2695874388384467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_89
      · exact prime_free64ElevenI_83459
      · exact prime_free64ElevenI_5853893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_11222326639 : Nat.Prime 11222326639 := by
  have hfermat : (6 : ZMod 11222326639) ^ (11222326639 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 11222326639) ^ ((11222326639 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 11222326639) ^ ((11222326639 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 11222326639) ^ ((11222326639 - 1) / 5021) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 11222326639) ^ ((11222326639 - 1) / 124171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11222326639 (6 : ZMod 11222326639)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5021, 1), (124171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5021, 1), (124171, 1)] : List FactorBlock).map factorBlockValue).prod = 11222326639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_5021
      · exact prime_free64ElevenI_124171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_4259748300978343 : Nat.Prime 4259748300978343 := by
  have hfermat : (3 : ZMod 4259748300978343) ^ (4259748300978343 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4259748300978343) ^ ((4259748300978343 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4259748300978343) ^ ((4259748300978343 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4259748300978343) ^ ((4259748300978343 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4259748300978343) ^ ((4259748300978343 - 1) / 1543) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 4259748300978343) ^ ((4259748300978343 - 1) / 11222326639) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4259748300978343 (3 : ZMod 4259748300978343)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (41, 1), (1543, 1), (11222326639, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (41, 1), (1543, 1), (11222326639, 1)] : List FactorBlock).map factorBlockValue).prod = 4259748300978343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_free64ElevenI_1543
      · exact prime_free64ElevenI_11222326639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_2692104817 : Nat.Prime 2692104817 := by
  have hfermat : (5 : ZMod 2692104817) ^ (2692104817 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 2692104817) ^ ((2692104817 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 2692104817) ^ ((2692104817 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 2692104817) ^ ((2692104817 - 1) / 653) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 2692104817) ^ ((2692104817 - 1) / 85889) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2692104817 (5 : ZMod 2692104817)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (653, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (653, 1), (85889, 1)] : List FactorBlock).map factorBlockValue).prod = 2692104817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_653
      · exact prime_free64ElevenI_85889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_10132269515533267 : Nat.Prime 10132269515533267 := by
  have hfermat : (2 : ZMod 10132269515533267) ^ (10132269515533267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 10132269515533267) ^ ((10132269515533267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 10132269515533267) ^ ((10132269515533267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 10132269515533267) ^ ((10132269515533267 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 10132269515533267) ^ ((10132269515533267 - 1) / 36899) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 10132269515533267) ^ ((10132269515533267 - 1) / 2692104817) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10132269515533267 (2 : ZMod 10132269515533267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (17, 1), (36899, 1), (2692104817, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (17, 1), (36899, 1), (2692104817, 1)] : List FactorBlock).map factorBlockValue).prod = 10132269515533267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_free64ElevenI_36899
      · exact prime_free64ElevenI_2692104817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_10279120799235109 : Nat.Prime 10279120799235109 := by
  have hfermat : (6 : ZMod 10279120799235109) ^ (10279120799235109 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 827) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 28687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 10279120799235109) ^ ((10279120799235109 - 1) / 104053) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 10279120799235109 (6 : ZMod 10279120799235109)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (347, 1), (827, 1), (28687, 1), (104053, 1)] : List FactorBlock).map factorBlockValue).prod = 10279120799235109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_347
      · exact prime_free64ElevenI_827
      · exact prime_free64ElevenI_28687
      · exact prime_free64ElevenI_104053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_11554931081 : Nat.Prime 11554931081 := by
  have hfermat : (3 : ZMod 11554931081) ^ (11554931081 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 11554931081) ^ ((11554931081 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 11554931081) ^ ((11554931081 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 11554931081) ^ ((11554931081 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 11554931081) ^ ((11554931081 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 11554931081) ^ ((11554931081 - 1) / 535943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11554931081 (3 : ZMod 11554931081)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (5, 1), (7, 2), (11, 1), (535943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (5, 1), (7, 2), (11, 1), (535943, 1)] : List FactorBlock).map factorBlockValue).prod = 11554931081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64ElevenI_535943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_23109862163 : Nat.Prime 23109862163 := by
  have hfermat : (2 : ZMod 23109862163) ^ (23109862163 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 23109862163) ^ ((23109862163 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 23109862163) ^ ((23109862163 - 1) / 11554931081) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 23109862163 (2 : ZMod 23109862163)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11554931081, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11554931081, 1)] : List FactorBlock).map factorBlockValue).prod = 23109862163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_11554931081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_74182657543231 : Nat.Prime 74182657543231 := by
  have hfermat : (3 : ZMod 74182657543231) ^ (74182657543231 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 74182657543231) ^ ((74182657543231 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 74182657543231) ^ ((74182657543231 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 74182657543231) ^ ((74182657543231 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 74182657543231) ^ ((74182657543231 - 1) / 107) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 74182657543231) ^ ((74182657543231 - 1) / 23109862163) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 74182657543231 (3 : ZMod 74182657543231)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (107, 1), (23109862163, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (107, 1), (23109862163, 1)] : List FactorBlock).map factorBlockValue).prod = 74182657543231 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_107
      · exact prime_free64ElevenI_23109862163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_8308457644841873 : Nat.Prime 8308457644841873 := by
  have hfermat : (3 : ZMod 8308457644841873) ^ (8308457644841873 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 8308457644841873) ^ ((8308457644841873 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 8308457644841873) ^ ((8308457644841873 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 8308457644841873) ^ ((8308457644841873 - 1) / 74182657543231) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 8308457644841873 (3 : ZMod 8308457644841873)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (74182657543231, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (74182657543231, 1)] : List FactorBlock).map factorBlockValue).prod = 8308457644841873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_74182657543231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_16616915289683747 : Nat.Prime 16616915289683747 := by
  have hfermat : (2 : ZMod 16616915289683747) ^ (16616915289683747 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 16616915289683747) ^ ((16616915289683747 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 16616915289683747) ^ ((16616915289683747 - 1) / 8308457644841873) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16616915289683747 (2 : ZMod 16616915289683747)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (8308457644841873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (8308457644841873, 1)] : List FactorBlock).map factorBlockValue).prod = 16616915289683747 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_8308457644841873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_14878103787467 : Nat.Prime 14878103787467 := by
  have hfermat : (2 : ZMod 14878103787467) ^ (14878103787467 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 547) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 14878103787467) ^ ((14878103787467 - 1) / 2557) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14878103787467 (2 : ZMod 14878103787467)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (43, 1), (179, 1), (547, 1), (691, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (43, 1), (179, 1), (547, 1), (691, 1), (2557, 1)] : List FactorBlock).map factorBlockValue).prod = 14878103787467 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_t64_179
      · exact prime_free64ElevenI_547
      · exact prime_free64ElevenI_691
      · exact prime_free64ElevenI_2557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_38831850885288871 : Nat.Prime 38831850885288871 := by
  have hfermat : (3 : ZMod 38831850885288871) ^ (38831850885288871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 38831850885288871) ^ ((38831850885288871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 38831850885288871) ^ ((38831850885288871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 38831850885288871) ^ ((38831850885288871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 38831850885288871) ^ ((38831850885288871 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 38831850885288871) ^ ((38831850885288871 - 1) / 14878103787467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 38831850885288871 (3 : ZMod 38831850885288871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (29, 1), (14878103787467, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (29, 1), (14878103787467, 1)] : List FactorBlock).map factorBlockValue).prod = 38831850885288871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_free64ElevenI_14878103787467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_17441309951587 : Nat.Prime 17441309951587 := by
  have hfermat : (2 : ZMod 17441309951587) ^ (17441309951587 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 17441309951587) ^ ((17441309951587 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 17441309951587) ^ ((17441309951587 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 17441309951587) ^ ((17441309951587 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 17441309951587) ^ ((17441309951587 - 1) / 5227) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 17441309951587) ^ ((17441309951587 - 1) / 8059837) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 17441309951587 (2 : ZMod 17441309951587)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (23, 1), (5227, 1), (8059837, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (23, 1), (5227, 1), (8059837, 1)] : List FactorBlock).map factorBlockValue).prod = 17441309951587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_23
      · exact prime_free64ElevenI_5227
      · exact prime_free64ElevenI_8059837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_80648617216138289 : Nat.Prime 80648617216138289 := by
  have hfermat : (3 : ZMod 80648617216138289) ^ (80648617216138289 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 80648617216138289) ^ ((80648617216138289 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 80648617216138289) ^ ((80648617216138289 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 80648617216138289) ^ ((80648617216138289 - 1) / 17441309951587) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 80648617216138289 (3 : ZMod 80648617216138289)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (17, 2), (17441309951587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (17, 2), (17441309951587, 1)] : List FactorBlock).map factorBlockValue).prod = 80648617216138289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64ElevenI_17441309951587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_281547015287347 : Nat.Prime 281547015287347 := by
  have hfermat : (2 : ZMod 281547015287347) ^ (281547015287347 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 281547015287347) ^ ((281547015287347 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 281547015287347) ^ ((281547015287347 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 281547015287347) ^ ((281547015287347 - 1) / 941) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 281547015287347) ^ ((281547015287347 - 1) / 12743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 281547015287347) ^ ((281547015287347 - 1) / 1304419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 281547015287347 (2 : ZMod 281547015287347)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (941, 1), (12743, 1), (1304419, 1)] : List FactorBlock).map factorBlockValue).prod = 281547015287347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_941
      · exact prime_free64ElevenI_12743
      · exact prime_free64ElevenI_1304419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_261838724217232711 : Nat.Prime 261838724217232711 := by
  have hfermat : (6 : ZMod 261838724217232711) ^ (261838724217232711 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 261838724217232711) ^ ((261838724217232711 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 261838724217232711) ^ ((261838724217232711 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 261838724217232711) ^ ((261838724217232711 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 261838724217232711) ^ ((261838724217232711 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 261838724217232711) ^ ((261838724217232711 - 1) / 281547015287347) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 261838724217232711 (6 : ZMod 261838724217232711)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (31, 1), (281547015287347, 1)] : List FactorBlock).map factorBlockValue).prod = 261838724217232711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_31
      · exact prime_free64ElevenI_281547015287347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_34091807 : Nat.Prime 34091807 := by
  have hfermat : (5 : ZMod 34091807) ^ (34091807 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 34091807) ^ ((34091807 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 34091807) ^ ((34091807 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 34091807) ^ ((34091807 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 34091807) ^ ((34091807 - 1) / 27361) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 34091807 (5 : ZMod 34091807)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (89, 1), (27361, 1)] : List FactorBlock).map factorBlockValue).prod = 34091807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_free64ElevenI_27361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_54819625657 : Nat.Prime 54819625657 := by
  have hfermat : (7 : ZMod 54819625657) ^ (54819625657 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 54819625657) ^ ((54819625657 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 54819625657) ^ ((54819625657 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 54819625657) ^ ((54819625657 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 54819625657) ^ ((54819625657 - 1) / 34091807) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 54819625657 (7 : ZMod 54819625657)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (67, 1), (34091807, 1)] : List FactorBlock).map factorBlockValue).prod = 54819625657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_free64ElevenI_34091807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_374376818878815937 : Nat.Prime 374376818878815937 := by
  have hfermat : (5 : ZMod 374376818878815937) ^ (374376818878815937 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 374376818878815937) ^ ((374376818878815937 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 374376818878815937) ^ ((374376818878815937 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 374376818878815937) ^ ((374376818878815937 - 1) / 35569) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 374376818878815937) ^ ((374376818878815937 - 1) / 54819625657) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 374376818878815937 (5 : ZMod 374376818878815937)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (35569, 1), (54819625657, 1)] : List FactorBlock).map factorBlockValue).prod = 374376818878815937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_35569
      · exact prime_free64ElevenI_54819625657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_423378269541287941 : Nat.Prime 423378269541287941 := by
  have hfermat : (21 : ZMod 423378269541287941) ^ (423378269541287941 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 2887) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 132857) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (21 : ZMod 423378269541287941) ^ ((423378269541287941 - 1) / 152041) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 423378269541287941 (21 : ZMod 423378269541287941)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (11, 2), (2887, 1), (132857, 1), (152041, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (11, 2), (2887, 1), (132857, 1), (152041, 1)] : List FactorBlock).map factorBlockValue).prod = 423378269541287941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64ElevenI_2887
      · exact prime_free64ElevenI_132857
      · exact prime_free64ElevenI_152041
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

private theorem prime_free64ElevenI_12098627 : Nat.Prime 12098627 := by
  have hfermat : (2 : ZMod 12098627) ^ (12098627 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 12098627) ^ ((12098627 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 12098627) ^ ((12098627 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 12098627) ^ ((12098627 - 1) / 7193) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 12098627 (2 : ZMod 12098627)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (29, 2), (7193, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (29, 2), (7193, 1)] : List FactorBlock).map factorBlockValue).prod = 12098627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_29
      · exact prime_free64ElevenI_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_435550573 : Nat.Prime 435550573 := by
  have hfermat : (7 : ZMod 435550573) ^ (435550573 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 435550573) ^ ((435550573 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 435550573) ^ ((435550573 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 435550573) ^ ((435550573 - 1) / 12098627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 435550573 (7 : ZMod 435550573)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 2), (12098627, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 2), (12098627, 1)] : List FactorBlock).map factorBlockValue).prod = 435550573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_12098627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_6587266866053 : Nat.Prime 6587266866053 := by
  have hfermat : (2 : ZMod 6587266866053) ^ (6587266866053 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 6587266866053) ^ ((6587266866053 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 6587266866053) ^ ((6587266866053 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 6587266866053) ^ ((6587266866053 - 1) / 199) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 6587266866053) ^ ((6587266866053 - 1) / 435550573) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6587266866053 (2 : ZMod 6587266866053)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (19, 1), (199, 1), (435550573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (19, 1), (199, 1), (435550573, 1)] : List FactorBlock).map factorBlockValue).prod = 6587266866053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_199
      · exact prime_free64ElevenI_435550573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1791736587566417 : Nat.Prime 1791736587566417 := by
  have hfermat : (3 : ZMod 1791736587566417) ^ (1791736587566417 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1791736587566417) ^ ((1791736587566417 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1791736587566417) ^ ((1791736587566417 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1791736587566417) ^ ((1791736587566417 - 1) / 6587266866053) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1791736587566417 (3 : ZMod 1791736587566417)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (17, 1), (6587266866053, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (17, 1), (6587266866053, 1)] : List FactorBlock).map factorBlockValue).prod = 1791736587566417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_17
      · exact prime_free64ElevenI_6587266866053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_473018459117534089 : Nat.Prime 473018459117534089 := by
  have hfermat : (17 : ZMod 473018459117534089) ^ (473018459117534089 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (17 : ZMod 473018459117534089) ^ ((473018459117534089 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (17 : ZMod 473018459117534089) ^ ((473018459117534089 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (17 : ZMod 473018459117534089) ^ ((473018459117534089 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (17 : ZMod 473018459117534089) ^ ((473018459117534089 - 1) / 1791736587566417) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 473018459117534089 (17 : ZMod 473018459117534089)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (11, 1), (1791736587566417, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (11, 1), (1791736587566417, 1)] : List FactorBlock).map factorBlockValue).prod = 473018459117534089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64ElevenI_1791736587566417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_19748623057 : Nat.Prime 19748623057 := by
  have hfermat : (10 : ZMod 19748623057) ^ (19748623057 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 19748623057) ^ ((19748623057 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 19748623057) ^ ((19748623057 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 19748623057) ^ ((19748623057 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (10 : ZMod 19748623057) ^ ((19748623057 - 1) / 157) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (10 : ZMod 19748623057) ^ ((19748623057 - 1) / 39113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 19748623057 (10 : ZMod 19748623057)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (67, 1), (157, 1), (39113, 1)] : List FactorBlock).map factorBlockValue).prod = 19748623057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_67
      · exact prime_t64_157
      · exact prime_free64ElevenI_39113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_554011756364663489 : Nat.Prime 554011756364663489 := by
  have hfermat : (3 : ZMod 554011756364663489) ^ (554011756364663489 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 554011756364663489) ^ ((554011756364663489 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 554011756364663489) ^ ((554011756364663489 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 554011756364663489) ^ ((554011756364663489 - 1) / 10691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 554011756364663489) ^ ((554011756364663489 - 1) / 19748623057) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 554011756364663489 (3 : ZMod 554011756364663489)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (41, 1), (10691, 1), (19748623057, 1)] : List FactorBlock).map factorBlockValue).prod = 554011756364663489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_41
      · exact prime_free64ElevenI_10691
      · exact prime_free64ElevenI_19748623057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_553872845191 : Nat.Prime 553872845191 := by
  have hfermat : (3 : ZMod 553872845191) ^ (553872845191 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 10159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 553872845191) ^ ((553872845191 - 1) / 259621) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 553872845191 (3 : ZMod 553872845191)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (7, 1), (10159, 1), (259621, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (7, 1), (10159, 1), (259621, 1)] : List FactorBlock).map factorBlockValue).prod = 553872845191 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64ElevenI_10159
      · exact prime_free64ElevenI_259621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_748110513271031791 : Nat.Prime 748110513271031791 := by
  have hfermat : (3 : ZMod 748110513271031791) ^ (748110513271031791 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 4093) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 748110513271031791) ^ ((748110513271031791 - 1) / 553872845191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 748110513271031791 (3 : ZMod 748110513271031791)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 1), (4093, 1), (553872845191, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 1), (4093, 1), (553872845191, 1)] : List FactorBlock).map factorBlockValue).prod = 748110513271031791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_free64ElevenI_4093
      · exact prime_free64ElevenI_553872845191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_2871090773 : Nat.Prime 2871090773 := by
  have hfermat : (2 : ZMod 2871090773) ^ (2871090773 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2871090773) ^ ((2871090773 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2871090773) ^ ((2871090773 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2871090773) ^ ((2871090773 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2871090773) ^ ((2871090773 - 1) / 1231171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2871090773 (2 : ZMod 2871090773)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (11, 1), (53, 1), (1231171, 1)] : List FactorBlock).map factorBlockValue).prod = 2871090773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_53
      · exact prime_free64ElevenI_1231171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_56020723162777 : Nat.Prime 56020723162777 := by
  have hfermat : (5 : ZMod 56020723162777) ^ (56020723162777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 56020723162777) ^ ((56020723162777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 56020723162777) ^ ((56020723162777 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 56020723162777) ^ ((56020723162777 - 1) / 271) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 56020723162777) ^ ((56020723162777 - 1) / 2871090773) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 56020723162777 (5 : ZMod 56020723162777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 2), (271, 1), (2871090773, 1)] : List FactorBlock).map factorBlockValue).prod = 56020723162777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_271
      · exact prime_free64ElevenI_2871090773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_859806059102301397 : Nat.Prime 859806059102301397 := by
  have hfermat : (2 : ZMod 859806059102301397) ^ (859806059102301397 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 859806059102301397) ^ ((859806059102301397 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 859806059102301397) ^ ((859806059102301397 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 859806059102301397) ^ ((859806059102301397 - 1) / 1279) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 859806059102301397) ^ ((859806059102301397 - 1) / 56020723162777) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 859806059102301397 (2 : ZMod 859806059102301397)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (1279, 1), (56020723162777, 1)] : List FactorBlock).map factorBlockValue).prod = 859806059102301397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_1279
      · exact prime_free64ElevenI_56020723162777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2867706713387 : Nat.Prime 2867706713387 := by
  have hfermat : (2 : ZMod 2867706713387) ^ (2867706713387 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2867706713387) ^ ((2867706713387 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2867706713387) ^ ((2867706713387 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2867706713387) ^ ((2867706713387 - 1) / 631) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2867706713387) ^ ((2867706713387 - 1) / 1637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2867706713387) ^ ((2867706713387 - 1) / 60353) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2867706713387 (2 : ZMod 2867706713387)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (23, 1), (631, 1), (1637, 1), (60353, 1)] : List FactorBlock).map factorBlockValue).prod = 2867706713387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_23
      · exact prime_free64ElevenI_631
      · exact prime_free64ElevenI_1637
      · exact prime_free64ElevenI_60353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_932050565158189193 : Nat.Prime 932050565158189193 := by
  have hfermat : (3 : ZMod 932050565158189193) ^ (932050565158189193 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 932050565158189193) ^ ((932050565158189193 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 932050565158189193) ^ ((932050565158189193 - 1) / 40627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 932050565158189193) ^ ((932050565158189193 - 1) / 2867706713387) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 932050565158189193 (3 : ZMod 932050565158189193)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (40627, 1), (2867706713387, 1)] : List FactorBlock).map factorBlockValue).prod = 932050565158189193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_40627
      · exact prime_free64ElevenI_2867706713387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_92285521 : Nat.Prime 92285521 := by
  have hfermat : (14 : ZMod 92285521) ^ (92285521 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (14 : ZMod 92285521) ^ ((92285521 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (14 : ZMod 92285521) ^ ((92285521 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (14 : ZMod 92285521) ^ ((92285521 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (14 : ZMod 92285521) ^ ((92285521 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (14 : ZMod 92285521) ^ ((92285521 - 1) / 22619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 92285521 (14 : ZMod 92285521)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (5, 1), (17, 1), (22619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (5, 1), (17, 1), (22619, 1)] : List FactorBlock).map factorBlockValue).prod = 92285521 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_17
      · exact prime_free64ElevenI_22619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1010126905894256753 : Nat.Prime 1010126905894256753 := by
  have hfermat : (3 : ZMod 1010126905894256753) ^ (1010126905894256753 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1010126905894256753) ^ ((1010126905894256753 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1010126905894256753) ^ ((1010126905894256753 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1010126905894256753) ^ ((1010126905894256753 - 1) / 277) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1010126905894256753) ^ ((1010126905894256753 - 1) / 352813) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1010126905894256753) ^ ((1010126905894256753 - 1) / 92285521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1010126905894256753 (3 : ZMod 1010126905894256753)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (277, 1), (352813, 1), (92285521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (277, 1), (352813, 1), (92285521, 1)] : List FactorBlock).map factorBlockValue).prod = 1010126905894256753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_277
      · exact prime_free64ElevenI_352813
      · exact prime_free64ElevenI_92285521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_39381871 : Nat.Prime 39381871 := by
  have hfermat : (7 : ZMod 39381871) ^ (39381871 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (7 : ZMod 39381871) ^ ((39381871 - 1) / 571) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 39381871 (7 : ZMod 39381871)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (11, 2), (19, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (11, 2), (19, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod = 39381871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_19
      · exact prime_free64ElevenI_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_4261197205943 : Nat.Prime 4261197205943 := by
  have hfermat : (5 : ZMod 4261197205943) ^ (4261197205943 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 4261197205943) ^ ((4261197205943 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 4261197205943) ^ ((4261197205943 - 1) / 54101) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 4261197205943) ^ ((4261197205943 - 1) / 39381871) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4261197205943 (5 : ZMod 4261197205943)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (54101, 1), (39381871, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (54101, 1), (39381871, 1)] : List FactorBlock).map factorBlockValue).prod = 4261197205943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_54101
      · exact prime_free64ElevenI_39381871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_5727049044787393 : Nat.Prime 5727049044787393 := by
  have hfermat : (5 : ZMod 5727049044787393) ^ (5727049044787393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 5727049044787393) ^ ((5727049044787393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 5727049044787393) ^ ((5727049044787393 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 5727049044787393) ^ ((5727049044787393 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 5727049044787393) ^ ((5727049044787393 - 1) / 4261197205943) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5727049044787393 (5 : ZMod 5727049044787393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 1), (7, 1), (4261197205943, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 1), (7, 1), (4261197205943, 1)] : List FactorBlock).map factorBlockValue).prod = 5727049044787393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64ElevenI_4261197205943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1122501612778329029 : Nat.Prime 1122501612778329029 := by
  have hfermat : (2 : ZMod 1122501612778329029) ^ (1122501612778329029 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1122501612778329029) ^ ((1122501612778329029 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1122501612778329029) ^ ((1122501612778329029 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1122501612778329029) ^ ((1122501612778329029 - 1) / 5727049044787393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1122501612778329029 (2 : ZMod 1122501612778329029)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 2), (5727049044787393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 2), (5727049044787393, 1)] : List FactorBlock).map factorBlockValue).prod = 1122501612778329029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_5727049044787393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_28778362928123 : Nat.Prime 28778362928123 := by
  have hfermat : (2 : ZMod 28778362928123) ^ (28778362928123 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 28778362928123) ^ ((28778362928123 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 28778362928123) ^ ((28778362928123 - 1) / 2029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 28778362928123) ^ ((28778362928123 - 1) / 6661) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 28778362928123) ^ ((28778362928123 - 1) / 1064669) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28778362928123 (2 : ZMod 28778362928123)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (2029, 1), (6661, 1), (1064669, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (2029, 1), (6661, 1), (1064669, 1)] : List FactorBlock).map factorBlockValue).prod = 28778362928123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_2029
      · exact prime_free64ElevenI_6661
      · exact prime_free64ElevenI_1064669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_57556725856247 : Nat.Prime 57556725856247 := by
  have hfermat : (5 : ZMod 57556725856247) ^ (57556725856247 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 57556725856247) ^ ((57556725856247 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 57556725856247) ^ ((57556725856247 - 1) / 28778362928123) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 57556725856247 (5 : ZMod 57556725856247)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (28778362928123, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (28778362928123, 1)] : List FactorBlock).map factorBlockValue).prod = 57556725856247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_28778362928123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_1757782407649783381 : Nat.Prime 1757782407649783381 := by
  have hfermat : (2 : ZMod 1757782407649783381) ^ (1757782407649783381 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1757782407649783381) ^ ((1757782407649783381 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1757782407649783381) ^ ((1757782407649783381 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1757782407649783381) ^ ((1757782407649783381 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 1757782407649783381) ^ ((1757782407649783381 - 1) / 509) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 1757782407649783381) ^ ((1757782407649783381 - 1) / 57556725856247) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1757782407649783381 (2 : ZMod 1757782407649783381)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (509, 1), (57556725856247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (509, 1), (57556725856247, 1)] : List FactorBlock).map factorBlockValue).prod = 1757782407649783381 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_509
      · exact prime_free64ElevenI_57556725856247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_279180007 : Nat.Prime 279180007 := by
  have hfermat : (3 : ZMod 279180007) ^ (279180007 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 279180007) ^ ((279180007 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 279180007) ^ ((279180007 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 279180007) ^ ((279180007 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 279180007) ^ ((279180007 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 279180007) ^ ((279180007 - 1) / 74687) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 279180007 (3 : ZMod 279180007)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (89, 1), (74687, 1)] : List FactorBlock).map factorBlockValue).prod = 279180007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_89
      · exact prime_free64ElevenI_74687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_110784210377741 : Nat.Prime 110784210377741 := by
  have hfermat : (7 : ZMod 110784210377741) ^ (110784210377741 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 110784210377741) ^ ((110784210377741 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 110784210377741) ^ ((110784210377741 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 110784210377741) ^ ((110784210377741 - 1) / 19841) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 110784210377741) ^ ((110784210377741 - 1) / 279180007) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 110784210377741 (7 : ZMod 110784210377741)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (19841, 1), (279180007, 1)] : List FactorBlock).map factorBlockValue).prod = 110784210377741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_19841
      · exact prime_free64ElevenI_279180007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_89292073564459247 : Nat.Prime 89292073564459247 := by
  have hfermat : (5 : ZMod 89292073564459247) ^ (89292073564459247 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 89292073564459247) ^ ((89292073564459247 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 89292073564459247) ^ ((89292073564459247 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 89292073564459247) ^ ((89292073564459247 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 89292073564459247) ^ ((89292073564459247 - 1) / 110784210377741) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 89292073564459247 (5 : ZMod 89292073564459247)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (13, 1), (31, 1), (110784210377741, 1)] : List FactorBlock).map factorBlockValue).prod = 89292073564459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_13
      · exact prime_t64_31
      · exact prime_free64ElevenI_110784210377741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2143009765547021929 : Nat.Prime 2143009765547021929 := by
  have hfermat : (7 : ZMod 2143009765547021929) ^ (2143009765547021929 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 2143009765547021929) ^ ((2143009765547021929 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 2143009765547021929) ^ ((2143009765547021929 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 2143009765547021929) ^ ((2143009765547021929 - 1) / 89292073564459247) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2143009765547021929 (7 : ZMod 2143009765547021929)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (89292073564459247, 1)] : List FactorBlock).map factorBlockValue).prod = 2143009765547021929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_89292073564459247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_2295461170901659093 : Nat.Prime 2295461170901659093 := by
  have hfermat : (2 : ZMod 2295461170901659093) ^ (2295461170901659093 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 1291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 4969) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 11717) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (2 : ZMod 2295461170901659093) ^ ((2295461170901659093 - 1) / 19427) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2295461170901659093 (2 : ZMod 2295461170901659093)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (131, 1), (1291, 1), (4969, 1), (11717, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (131, 1), (1291, 1), (4969, 1), (11717, 1), (19427, 1)] : List FactorBlock).map factorBlockValue).prod = 2295461170901659093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_131
      · exact prime_free64ElevenI_1291
      · exact prime_free64ElevenI_4969
      · exact prime_free64ElevenI_11717
      · exact prime_free64ElevenI_19427
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

private theorem prime_free64ElevenI_21609402770898839089 : Nat.Prime 21609402770898839089 := by
  have hfermat : (22 : ZMod 21609402770898839089) ^ (21609402770898839089 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 1009) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 706841) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (22 : ZMod 21609402770898839089) ^ ((21609402770898839089 - 1) / 5131963) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21609402770898839089 (22 : ZMod 21609402770898839089)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 2), (41, 1), (1009, 1), (706841, 1), (5131963, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 2), (41, 1), (1009, 1), (706841, 1), (5131963, 1)] : List FactorBlock).map factorBlockValue).prod = 21609402770898839089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_41
      · exact prime_free64ElevenI_1009
      · exact prime_free64ElevenI_706841
      · exact prime_free64ElevenI_5131963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_365348072111507 : Nat.Prime 365348072111507 := by
  have hfermat : (5 : ZMod 365348072111507) ^ (365348072111507 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 365348072111507) ^ ((365348072111507 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 365348072111507) ^ ((365348072111507 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 365348072111507) ^ ((365348072111507 - 1) / 431) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 365348072111507) ^ ((365348072111507 - 1) / 59693) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 365348072111507) ^ ((365348072111507 - 1) / 645481) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 365348072111507 (5 : ZMod 365348072111507)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (431, 1), (59693, 1), (645481, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (431, 1), (59693, 1), (645481, 1)] : List FactorBlock).map factorBlockValue).prod = 365348072111507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_t64_431
      · exact prime_free64ElevenI_59693
      · exact prime_free64ElevenI_645481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_32098750919572782007 : Nat.Prime 32098750919572782007 := by
  have hfermat : (3 : ZMod 32098750919572782007) ^ (32098750919572782007 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 32098750919572782007) ^ ((32098750919572782007 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 32098750919572782007) ^ ((32098750919572782007 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 32098750919572782007) ^ ((32098750919572782007 - 1) / 1627) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 32098750919572782007) ^ ((32098750919572782007 - 1) / 365348072111507) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 32098750919572782007 (3 : ZMod 32098750919572782007)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (1627, 1), (365348072111507, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (1627, 1), (365348072111507, 1)] : List FactorBlock).map factorBlockValue).prod = 32098750919572782007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_1627
      · exact prime_free64ElevenI_365348072111507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_348552456619 : Nat.Prime 348552456619 := by
  have hfermat : (3 : ZMod 348552456619) ^ (348552456619 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 348552456619) ^ ((348552456619 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 348552456619) ^ ((348552456619 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 348552456619) ^ ((348552456619 - 1) / 32377) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 348552456619) ^ ((348552456619 - 1) / 1794239) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 348552456619 (3 : ZMod 348552456619)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (32377, 1), (1794239, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (32377, 1), (1794239, 1)] : List FactorBlock).map factorBlockValue).prod = 348552456619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_32377
      · exact prime_free64ElevenI_1794239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_44793316211528141791 : Nat.Prime 44793316211528141791 := by
  have hfermat : (6 : ZMod 44793316211528141791) ^ (44793316211528141791 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 329519) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 44793316211528141791) ^ ((44793316211528141791 - 1) / 348552456619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 44793316211528141791 (6 : ZMod 44793316211528141791)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (13, 1), (329519, 1), (348552456619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (13, 1), (329519, 1), (348552456619, 1)] : List FactorBlock).map factorBlockValue).prod = 44793316211528141791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_free64ElevenI_329519
      · exact prime_free64ElevenI_348552456619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_55379759 : Nat.Prime 55379759 := by
  have hfermat : (7 : ZMod 55379759) ^ (55379759 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 55379759) ^ ((55379759 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 55379759) ^ ((55379759 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 55379759) ^ ((55379759 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 55379759) ^ ((55379759 - 1) / 47659) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 55379759 (7 : ZMod 55379759)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 1), (83, 1), (47659, 1)] : List FactorBlock).map factorBlockValue).prod = 55379759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_83
      · exact prime_free64ElevenI_47659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_260519272661 : Nat.Prime 260519272661 := by
  have hfermat : (3 : ZMod 260519272661) ^ (260519272661 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 260519272661) ^ ((260519272661 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 260519272661) ^ ((260519272661 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 260519272661) ^ ((260519272661 - 1) / 25439) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 260519272661) ^ ((260519272661 - 1) / 512047) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 260519272661 (3 : ZMod 260519272661)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (25439, 1), (512047, 1)] : List FactorBlock).map factorBlockValue).prod = 260519272661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_25439
      · exact prime_free64ElevenI_512047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_57709978139285874797 : Nat.Prime 57709978139285874797 := by
  have hfermat : (2 : ZMod 57709978139285874797) ^ (57709978139285874797 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 57709978139285874797) ^ ((57709978139285874797 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 57709978139285874797) ^ ((57709978139285874797 - 1) / 55379759) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 57709978139285874797) ^ ((57709978139285874797 - 1) / 260519272661) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 57709978139285874797 (2 : ZMod 57709978139285874797)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (55379759, 1), (260519272661, 1)] : List FactorBlock).map factorBlockValue).prod = 57709978139285874797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_55379759
      · exact prime_free64ElevenI_260519272661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_22140787 : Nat.Prime 22140787 := by
  have hfermat : (2 : ZMod 22140787) ^ (22140787 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 22140787) ^ ((22140787 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 22140787) ^ ((22140787 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 22140787) ^ ((22140787 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 22140787) ^ ((22140787 - 1) / 85817) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 22140787 (2 : ZMod 22140787)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (85817, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (85817, 1)] : List FactorBlock).map factorBlockValue).prod = 22140787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_free64ElevenI_85817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_140392491357773839 : Nat.Prime 140392491357773839 := by
  have hfermat : (6 : ZMod 140392491357773839) ^ (140392491357773839 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 1559) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 14423) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 140392491357773839) ^ ((140392491357773839 - 1) / 22140787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 140392491357773839 (6 : ZMod 140392491357773839)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (47, 1), (1559, 1), (14423, 1), (22140787, 1)] : List FactorBlock).map factorBlockValue).prod = 140392491357773839 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_47
      · exact prime_free64ElevenI_1559
      · exact prime_free64ElevenI_14423
      · exact prime_free64ElevenI_22140787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_110910068172641332811 : Nat.Prime 110910068172641332811 := by
  have hfermat : (2 : ZMod 110910068172641332811) ^ (110910068172641332811 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 110910068172641332811) ^ ((110910068172641332811 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 110910068172641332811) ^ ((110910068172641332811 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 110910068172641332811) ^ ((110910068172641332811 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 110910068172641332811) ^ ((110910068172641332811 - 1) / 140392491357773839) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 110910068172641332811 (2 : ZMod 110910068172641332811)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (79, 1), (140392491357773839, 1)] : List FactorBlock).map factorBlockValue).prod = 110910068172641332811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_79
      · exact prime_free64ElevenI_140392491357773839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2810709763 : Nat.Prime 2810709763 := by
  have hfermat : (2 : ZMod 2810709763) ^ (2810709763 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2810709763) ^ ((2810709763 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2810709763) ^ ((2810709763 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2810709763) ^ ((2810709763 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2810709763) ^ ((2810709763 - 1) / 4973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2810709763) ^ ((2810709763 - 1) / 13457) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2810709763 (2 : ZMod 2810709763)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (4973, 1), (13457, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (4973, 1), (13457, 1)] : List FactorBlock).map factorBlockValue).prod = 2810709763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64ElevenI_4973
      · exact prime_free64ElevenI_13457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_340500623528873 : Nat.Prime 340500623528873 := by
  have hfermat : (3 : ZMod 340500623528873) ^ (340500623528873 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 340500623528873) ^ ((340500623528873 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 340500623528873) ^ ((340500623528873 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 340500623528873) ^ ((340500623528873 - 1) / 797) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 340500623528873) ^ ((340500623528873 - 1) / 2810709763) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 340500623528873 (3 : ZMod 340500623528873)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (19, 1), (797, 1), (2810709763, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (19, 1), (797, 1), (2810709763, 1)] : List FactorBlock).map factorBlockValue).prod = 340500623528873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_797
      · exact prime_free64ElevenI_2810709763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_591109082446123529 : Nat.Prime 591109082446123529 := by
  have hfermat : (3 : ZMod 591109082446123529) ^ (591109082446123529 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 591109082446123529) ^ ((591109082446123529 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 591109082446123529) ^ ((591109082446123529 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 591109082446123529) ^ ((591109082446123529 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 591109082446123529) ^ ((591109082446123529 - 1) / 340500623528873) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 591109082446123529 (3 : ZMod 591109082446123529)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (31, 1), (340500623528873, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (31, 1), (340500623528873, 1)] : List FactorBlock).map factorBlockValue).prod = 591109082446123529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_31
      · exact prime_free64ElevenI_340500623528873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_117039598324332458743 : Nat.Prime 117039598324332458743 := by
  have hfermat : (6 : ZMod 117039598324332458743) ^ (117039598324332458743 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 117039598324332458743) ^ ((117039598324332458743 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 117039598324332458743) ^ ((117039598324332458743 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 117039598324332458743) ^ ((117039598324332458743 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 117039598324332458743) ^ ((117039598324332458743 - 1) / 591109082446123529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 117039598324332458743 (6 : ZMod 117039598324332458743)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (11, 1), (591109082446123529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (11, 1), (591109082446123529, 1)] : List FactorBlock).map factorBlockValue).prod = 117039598324332458743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64ElevenI_591109082446123529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_99081140707 : Nat.Prime 99081140707 := by
  have hfermat : (2 : ZMod 99081140707) ^ (99081140707 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 99081140707) ^ ((99081140707 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 99081140707) ^ ((99081140707 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 99081140707) ^ ((99081140707 - 1) / 24077) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 99081140707) ^ ((99081140707 - 1) / 76207) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 99081140707 (2 : ZMod 99081140707)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (24077, 1), (76207, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (24077, 1), (76207, 1)] : List FactorBlock).map factorBlockValue).prod = 99081140707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_24077
      · exact prime_free64ElevenI_76207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2310592769937563928959 : Nat.Prime 2310592769937563928959 := by
  have hfermat : (7 : ZMod 2310592769937563928959) ^ (2310592769937563928959 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 2310592769937563928959) ^ ((2310592769937563928959 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 2310592769937563928959) ^ ((2310592769937563928959 - 1) / 41131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 2310592769937563928959) ^ ((2310592769937563928959 - 1) / 283487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 2310592769937563928959) ^ ((2310592769937563928959 - 1) / 99081140707) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2310592769937563928959 (7 : ZMod 2310592769937563928959)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (41131, 1), (283487, 1), (99081140707, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (41131, 1), (283487, 1), (99081140707, 1)] : List FactorBlock).map factorBlockValue).prod = 2310592769937563928959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_41131
      · exact prime_free64ElevenI_283487
      · exact prime_free64ElevenI_99081140707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2192725397572529 : Nat.Prime 2192725397572529 := by
  have hfermat : (3 : ZMod 2192725397572529) ^ (2192725397572529 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 421) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 2192725397572529) ^ ((2192725397572529 - 1) / 4663859) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2192725397572529 (3 : ZMod 2192725397572529)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (7, 1), (13, 2), (59, 1), (421, 1), (4663859, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (7, 1), (13, 2), (59, 1), (421, 1), (4663859, 1)] : List FactorBlock).map factorBlockValue).prod = 2192725397572529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_13
      · exact prime_t64_59
      · exact prime_t64_421
      · exact prime_free64ElevenI_4663859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_2853827719489851348443 : Nat.Prime 2853827719489851348443 := by
  have hfermat : (2 : ZMod 2853827719489851348443) ^ (2853827719489851348443 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2853827719489851348443) ^ ((2853827719489851348443 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2853827719489851348443) ^ ((2853827719489851348443 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2853827719489851348443) ^ ((2853827719489851348443 - 1) / 59159) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2853827719489851348443) ^ ((2853827719489851348443 - 1) / 2192725397572529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2853827719489851348443 (2 : ZMod 2853827719489851348443)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (11, 1), (59159, 1), (2192725397572529, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (11, 1), (59159, 1), (2192725397572529, 1)] : List FactorBlock).map factorBlockValue).prod = 2853827719489851348443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64ElevenI_59159
      · exact prime_free64ElevenI_2192725397572529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_190507613573 : Nat.Prime 190507613573 := by
  have hfermat : (2 : ZMod 190507613573) ^ (190507613573 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 190507613573) ^ ((190507613573 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 190507613573) ^ ((190507613573 - 1) / 727) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 190507613573) ^ ((190507613573 - 1) / 3691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 190507613573) ^ ((190507613573 - 1) / 17749) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 190507613573 (2 : ZMod 190507613573)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (727, 1), (3691, 1), (17749, 1)] : List FactorBlock).map factorBlockValue).prod = 190507613573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_727
      · exact prime_free64ElevenI_3691
      · exact prime_free64ElevenI_17749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1143045681439 : Nat.Prime 1143045681439 := by
  have hfermat : (6 : ZMod 1143045681439) ^ (1143045681439 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1143045681439) ^ ((1143045681439 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1143045681439) ^ ((1143045681439 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1143045681439) ^ ((1143045681439 - 1) / 190507613573) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1143045681439 (6 : ZMod 1143045681439)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (190507613573, 1)] : List FactorBlock).map factorBlockValue).prod = 1143045681439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_190507613573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_558234740355005780371 : Nat.Prime 558234740355005780371 := by
  have hfermat : (2 : ZMod 558234740355005780371) ^ (558234740355005780371 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 558234740355005780371) ^ ((558234740355005780371 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 558234740355005780371) ^ ((558234740355005780371 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 558234740355005780371) ^ ((558234740355005780371 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 558234740355005780371) ^ ((558234740355005780371 - 1) / 5426387) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 558234740355005780371) ^ ((558234740355005780371 - 1) / 1143045681439) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 558234740355005780371 (2 : ZMod 558234740355005780371)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (5426387, 1), (1143045681439, 1)] : List FactorBlock).map factorBlockValue).prod = 558234740355005780371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_5426387
      · exact prime_free64ElevenI_1143045681439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_3349408442130034682227 : Nat.Prime 3349408442130034682227 := by
  have hfermat : (2 : ZMod 3349408442130034682227) ^ (3349408442130034682227 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 3349408442130034682227) ^ ((3349408442130034682227 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 3349408442130034682227) ^ ((3349408442130034682227 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 3349408442130034682227) ^ ((3349408442130034682227 - 1) / 558234740355005780371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3349408442130034682227 (2 : ZMod 3349408442130034682227)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (558234740355005780371, 1)] : List FactorBlock).map factorBlockValue).prod = 3349408442130034682227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_558234740355005780371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_80744533 : Nat.Prime 80744533 := by
  have hfermat : (6 : ZMod 80744533) ^ (80744533 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 80744533) ^ ((80744533 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 80744533) ^ ((80744533 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 80744533) ^ ((80744533 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 80744533) ^ ((80744533 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 80744533) ^ ((80744533 - 1) / 4051) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 80744533 (6 : ZMod 80744533)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (11, 1), (151, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod = 80744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_free64ElevenI_151
      · exact prime_free64ElevenI_4051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_5118840821 : Nat.Prime 5118840821 := by
  have hfermat : (2 : ZMod 5118840821) ^ (5118840821 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5118840821) ^ ((5118840821 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5118840821) ^ ((5118840821 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5118840821) ^ ((5118840821 - 1) / 1291) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5118840821) ^ ((5118840821 - 1) / 198251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5118840821 (2 : ZMod 5118840821)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (1291, 1), (198251, 1)] : List FactorBlock).map factorBlockValue).prod = 5118840821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_1291
      · exact prime_free64ElevenI_198251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_826636823185963187 : Nat.Prime 826636823185963187 := by
  have hfermat : (2 : ZMod 826636823185963187) ^ (826636823185963187 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 826636823185963187) ^ ((826636823185963187 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 826636823185963187) ^ ((826636823185963187 - 1) / 80744533) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 826636823185963187) ^ ((826636823185963187 - 1) / 5118840821) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 826636823185963187 (2 : ZMod 826636823185963187)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (80744533, 1), (5118840821, 1)] : List FactorBlock).map factorBlockValue).prod = 826636823185963187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_80744533
      · exact prime_free64ElevenI_5118840821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_4430773372276762682321 : Nat.Prime 4430773372276762682321 := by
  have hfermat : (3 : ZMod 4430773372276762682321) ^ (4430773372276762682321 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4430773372276762682321) ^ ((4430773372276762682321 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4430773372276762682321) ^ ((4430773372276762682321 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4430773372276762682321) ^ ((4430773372276762682321 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4430773372276762682321) ^ ((4430773372276762682321 - 1) / 826636823185963187) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4430773372276762682321 (3 : ZMod 4430773372276762682321)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (67, 1), (826636823185963187, 1)] : List FactorBlock).map factorBlockValue).prod = 4430773372276762682321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_67
      · exact prime_free64ElevenI_826636823185963187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_628384961 : Nat.Prime 628384961 := by
  have hfermat : (6 : ZMod 628384961) ^ (628384961 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 67) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 628384961) ^ ((628384961 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 628384961 (6 : ZMod 628384961)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (5, 1), (7, 1), (53, 1), (67, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (5, 1), (7, 1), (53, 1), (67, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod = 628384961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_53
      · exact prime_t64_67
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

private theorem prime_free64ElevenI_9109483663880487566509 : Nat.Prime 9109483663880487566509 := by
  have hfermat : (2 : ZMod 9109483663880487566509) ^ (9109483663880487566509 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 11933) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 565567) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 9109483663880487566509) ^ ((9109483663880487566509 - 1) / 628384961) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9109483663880487566509 (2 : ZMod 9109483663880487566509)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (179, 1), (11933, 1), (565567, 1), (628384961, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (179, 1), (11933, 1), (565567, 1), (628384961, 1)] : List FactorBlock).map factorBlockValue).prod = 9109483663880487566509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_179
      · exact prime_free64ElevenI_11933
      · exact prime_free64ElevenI_565567
      · exact prime_free64ElevenI_628384961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_1054347127343 : Nat.Prime 1054347127343 := by
  have hfermat : (5 : ZMod 1054347127343) ^ (1054347127343 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 1054347127343) ^ ((1054347127343 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 1054347127343) ^ ((1054347127343 - 1) / 137909) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 1054347127343) ^ ((1054347127343 - 1) / 3822619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1054347127343 (5 : ZMod 1054347127343)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (137909, 1), (3822619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (137909, 1), (3822619, 1)] : List FactorBlock).map factorBlockValue).prod = 1054347127343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_137909
      · exact prime_free64ElevenI_3822619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_50681942350247058416537 : Nat.Prime 50681942350247058416537 := by
  have hfermat : (3 : ZMod 50681942350247058416537) ^ (50681942350247058416537 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 50681942350247058416537) ^ ((50681942350247058416537 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 50681942350247058416537) ^ ((50681942350247058416537 - 1) / 46273) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 50681942350247058416537) ^ ((50681942350247058416537 - 1) / 129853) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 50681942350247058416537) ^ ((50681942350247058416537 - 1) / 1054347127343) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 50681942350247058416537 (3 : ZMod 50681942350247058416537)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (46273, 1), (129853, 1), (1054347127343, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (46273, 1), (129853, 1), (1054347127343, 1)] : List FactorBlock).map factorBlockValue).prod = 50681942350247058416537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_46273
      · exact prime_free64ElevenI_129853
      · exact prime_free64ElevenI_1054347127343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_21160721 : Nat.Prime 21160721 := by
  have hfermat : (12 : ZMod 21160721) ^ (21160721 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (12 : ZMod 21160721) ^ ((21160721 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (12 : ZMod 21160721) ^ ((21160721 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (12 : ZMod 21160721) ^ ((21160721 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (12 : ZMod 21160721) ^ ((21160721 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (12 : ZMod 21160721) ^ ((21160721 - 1) / 1303) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 21160721 (12 : ZMod 21160721)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (7, 1), (29, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (7, 1), (29, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod = 21160721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_29
      · exact prime_free64ElevenI_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_4819414370321 : Nat.Prime 4819414370321 := by
  have hfermat : (3 : ZMod 4819414370321) ^ (4819414370321 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 2081) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 4819414370321) ^ ((4819414370321 - 1) / 154807) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4819414370321 (3 : ZMod 4819414370321)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (5, 1), (11, 1), (17, 1), (2081, 1), (154807, 1)] : List FactorBlock).map factorBlockValue).prod = 4819414370321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_17
      · exact prime_free64ElevenI_2081
      · exact prime_free64ElevenI_154807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_269887204737977 : Nat.Prime 269887204737977 := by
  have hfermat : (3 : ZMod 269887204737977) ^ (269887204737977 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 269887204737977) ^ ((269887204737977 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 269887204737977) ^ ((269887204737977 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 269887204737977) ^ ((269887204737977 - 1) / 4819414370321) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 269887204737977 (3 : ZMod 269887204737977)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (7, 1), (4819414370321, 1)] : List FactorBlock).map factorBlockValue).prod = 269887204737977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_4819414370321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_57110078409302094014171 : Nat.Prime 57110078409302094014171 := by
  have hfermat : (6 : ZMod 57110078409302094014171) ^ (57110078409302094014171 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 57110078409302094014171) ^ ((57110078409302094014171 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 57110078409302094014171) ^ ((57110078409302094014171 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 57110078409302094014171) ^ ((57110078409302094014171 - 1) / 21160721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 57110078409302094014171) ^ ((57110078409302094014171 - 1) / 269887204737977) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 57110078409302094014171 (6 : ZMod 57110078409302094014171)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (21160721, 1), (269887204737977, 1)] : List FactorBlock).map factorBlockValue).prod = 57110078409302094014171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_21160721
      · exact prime_free64ElevenI_269887204737977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_11540831 : Nat.Prime 11540831 := by
  have hfermat : (7 : ZMod 11540831) ^ (11540831 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (7 : ZMod 11540831) ^ ((11540831 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (7 : ZMod 11540831) ^ ((11540831 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (7 : ZMod 11540831) ^ ((11540831 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (7 : ZMod 11540831) ^ ((11540831 - 1) / 173) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (7 : ZMod 11540831) ^ ((11540831 - 1) / 953) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11540831 (7 : ZMod 11540831)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (7, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (7, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod = 11540831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_free64ElevenI_173
      · exact prime_free64ElevenI_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_2909674311721 : Nat.Prime 2909674311721 := by
  have hfermat : (13 : ZMod 2909674311721) ^ (2909674311721 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 191) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (13 : ZMod 2909674311721) ^ ((2909674311721 - 1) / 11540831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2909674311721 (13 : ZMod 2909674311721)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (11, 1), (191, 1), (11540831, 1)] : List FactorBlock).map factorBlockValue).prod = 2909674311721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_11
      · exact prime_t64_191
      · exact prime_free64ElevenI_11540831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_67024695540586320517363 : Nat.Prime 67024695540586320517363 := by
  have hfermat : (3 : ZMod 67024695540586320517363) ^ (67024695540586320517363 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 1899647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 67024695540586320517363) ^ ((67024695540586320517363 - 1) / 2909674311721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 67024695540586320517363 (3 : ZMod 67024695540586320517363)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (43, 1), (47, 1), (1899647, 1), (2909674311721, 1)] : List FactorBlock).map factorBlockValue).prod = 67024695540586320517363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_43
      · exact prime_t64_47
      · exact prime_free64ElevenI_1899647
      · exact prime_free64ElevenI_2909674311721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_105371323 : Nat.Prime 105371323 := by
  have hfermat : (3 : ZMod 105371323) ^ (105371323 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 105371323) ^ ((105371323 - 1) / 181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 105371323 (3 : ZMod 105371323)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (83, 1), (167, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (83, 1), (167, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod = 105371323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_83
      · exact prime_t64_167
      · exact prime_free64ElevenI_181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_6949449494497 : Nat.Prime 6949449494497 := by
  have hfermat : (5 : ZMod 6949449494497) ^ (6949449494497 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 6949449494497) ^ ((6949449494497 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 6949449494497) ^ ((6949449494497 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 6949449494497) ^ ((6949449494497 - 1) / 229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 6949449494497) ^ ((6949449494497 - 1) / 105371323) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6949449494497 (5 : ZMod 6949449494497)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (229, 1), (105371323, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (229, 1), (105371323, 1)] : List FactorBlock).map factorBlockValue).prod = 6949449494497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_229
      · exact prime_free64ElevenI_105371323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_333573575735857 : Nat.Prime 333573575735857 := by
  have hfermat : (10 : ZMod 333573575735857) ^ (333573575735857 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (10 : ZMod 333573575735857) ^ ((333573575735857 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (10 : ZMod 333573575735857) ^ ((333573575735857 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (10 : ZMod 333573575735857) ^ ((333573575735857 - 1) / 6949449494497) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 333573575735857 (10 : ZMod 333573575735857)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (6949449494497, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (6949449494497, 1)] : List FactorBlock).map factorBlockValue).prod = 333573575735857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_6949449494497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_69095803359603035568841 : Nat.Prime 69095803359603035568841 := by
  have hfermat : (22 : ZMod 69095803359603035568841) ^ (69095803359603035568841 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 83) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 2971) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (22 : ZMod 69095803359603035568841) ^ ((69095803359603035568841 - 1) / 333573575735857) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 69095803359603035568841 (22 : ZMod 69095803359603035568841)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 1), (5, 1), (7, 1), (83, 1), (2971, 1), (333573575735857, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 1), (5, 1), (7, 1), (83, 1), (2971, 1), (333573575735857, 1)] : List FactorBlock).map factorBlockValue).prod = 69095803359603035568841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_7
      · exact prime_t64_83
      · exact prime_free64ElevenI_2971
      · exact prime_free64ElevenI_333573575735857
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

private theorem prime_free64ElevenI_35214997 : Nat.Prime 35214997 := by
  have hfermat : (2 : ZMod 35214997) ^ (35214997 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 35214997) ^ ((35214997 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 35214997) ^ ((35214997 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 35214997) ^ ((35214997 - 1) / 2934583) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 35214997 (2 : ZMod 35214997)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (2934583, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (2934583, 1)] : List FactorBlock).map factorBlockValue).prod = 35214997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_2934583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_30049397069 : Nat.Prime 30049397069 := by
  have hfermat : (2 : ZMod 30049397069) ^ (30049397069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 30049397069) ^ ((30049397069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 30049397069) ^ ((30049397069 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 30049397069) ^ ((30049397069 - 1) / 257) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 30049397069) ^ ((30049397069 - 1) / 467) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 30049397069) ^ ((30049397069 - 1) / 1181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 30049397069 (2 : ZMod 30049397069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (53, 1), (257, 1), (467, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (53, 1), (257, 1), (467, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod = 30049397069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_free64ElevenI_257
      · exact prime_t64_467
      · exact prime_free64ElevenI_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_2116378855273287587 : Nat.Prime 2116378855273287587 := by
  have hfermat : (2 : ZMod 2116378855273287587) ^ (2116378855273287587 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2116378855273287587) ^ ((2116378855273287587 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2116378855273287587) ^ ((2116378855273287587 - 1) / 35214997) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2116378855273287587) ^ ((2116378855273287587 - 1) / 30049397069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2116378855273287587 (2 : ZMod 2116378855273287587)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (35214997, 1), (30049397069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (35214997, 1), (30049397069, 1)] : List FactorBlock).map factorBlockValue).prod = 2116378855273287587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_35214997
      · exact prime_free64ElevenI_30049397069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_83076335584897630940099 : Nat.Prime 83076335584897630940099 := by
  have hfermat : (2 : ZMod 83076335584897630940099) ^ (83076335584897630940099 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 83076335584897630940099) ^ ((83076335584897630940099 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 83076335584897630940099) ^ ((83076335584897630940099 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 83076335584897630940099) ^ ((83076335584897630940099 - 1) / 1033) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 83076335584897630940099) ^ ((83076335584897630940099 - 1) / 2116378855273287587) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 83076335584897630940099 (2 : ZMod 83076335584897630940099)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (1033, 1), (2116378855273287587, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (1033, 1), (2116378855273287587, 1)] : List FactorBlock).map factorBlockValue).prod = 83076335584897630940099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_1033
      · exact prime_free64ElevenI_2116378855273287587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_51319799 : Nat.Prime 51319799 := by
  have hfermat : (11 : ZMod 51319799) ^ (51319799 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 51319799) ^ ((51319799 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 51319799) ^ ((51319799 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 51319799) ^ ((51319799 - 1) / 1350521) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 51319799 (11 : ZMod 51319799)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (19, 1), (1350521, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (19, 1), (1350521, 1)] : List FactorBlock).map factorBlockValue).prod = 51319799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_19
      · exact prime_free64ElevenI_1350521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_2105959469695740377171 : Nat.Prime 2105959469695740377171 := by
  have hfermat : (2 : ZMod 2105959469695740377171) ^ (2105959469695740377171 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 8231) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 9029) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 55217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 2105959469695740377171) ^ ((2105959469695740377171 - 1) / 51319799) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2105959469695740377171 (2 : ZMod 2105959469695740377171)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (8231, 1), (9029, 1), (55217, 1), (51319799, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (8231, 1), (9029, 1), (55217, 1), (51319799, 1)] : List FactorBlock).map factorBlockValue).prod = 2105959469695740377171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_8231
      · exact prime_free64ElevenI_9029
      · exact prime_free64ElevenI_55217
      · exact prime_free64ElevenI_51319799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_88450297727221095841183 : Nat.Prime 88450297727221095841183 := by
  have hfermat : (3 : ZMod 88450297727221095841183) ^ (88450297727221095841183 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 88450297727221095841183) ^ ((88450297727221095841183 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 88450297727221095841183) ^ ((88450297727221095841183 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 88450297727221095841183) ^ ((88450297727221095841183 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 88450297727221095841183) ^ ((88450297727221095841183 - 1) / 2105959469695740377171) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 88450297727221095841183 (3 : ZMod 88450297727221095841183)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (2105959469695740377171, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (2105959469695740377171, 1)] : List FactorBlock).map factorBlockValue).prod = 88450297727221095841183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_free64ElevenI_2105959469695740377171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_4592656007 : Nat.Prime 4592656007 := by
  have hfermat : (5 : ZMod 4592656007) ^ (4592656007 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 4592656007) ^ ((4592656007 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 4592656007) ^ ((4592656007 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 4592656007) ^ ((4592656007 - 1) / 1487) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 4592656007) ^ ((4592656007 - 1) / 41737) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4592656007 (5 : ZMod 4592656007)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (37, 1), (1487, 1), (41737, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (37, 1), (1487, 1), (41737, 1)] : List FactorBlock).map factorBlockValue).prod = 4592656007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_37
      · exact prime_free64ElevenI_1487
      · exact prime_free64ElevenI_41737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_91853120141 : Nat.Prime 91853120141 := by
  have hfermat : (2 : ZMod 91853120141) ^ (91853120141 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 91853120141) ^ ((91853120141 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 91853120141) ^ ((91853120141 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 91853120141) ^ ((91853120141 - 1) / 4592656007) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 91853120141 (2 : ZMod 91853120141)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (5, 1), (4592656007, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (5, 1), (4592656007, 1)] : List FactorBlock).map factorBlockValue).prod = 91853120141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_4592656007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1102237441693 : Nat.Prime 1102237441693 := by
  have hfermat : (2 : ZMod 1102237441693) ^ (1102237441693 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1102237441693) ^ ((1102237441693 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1102237441693) ^ ((1102237441693 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1102237441693) ^ ((1102237441693 - 1) / 91853120141) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1102237441693 (2 : ZMod 1102237441693)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (91853120141, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (91853120141, 1)] : List FactorBlock).map factorBlockValue).prod = 1102237441693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_91853120141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_174018649393588440750739 : Nat.Prime 174018649393588440750739 := by
  have hfermat : (11 : ZMod 174018649393588440750739) ^ (174018649393588440750739 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 1283) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 143419) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (11 : ZMod 174018649393588440750739) ^ ((174018649393588440750739 - 1) / 1102237441693) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 174018649393588440750739 (11 : ZMod 174018649393588440750739)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (13, 1), (1283, 1), (143419, 1), (1102237441693, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (13, 1), (1283, 1), (143419, 1), (1102237441693, 1)] : List FactorBlock).map factorBlockValue).prod = 174018649393588440750739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_13
      · exact prime_free64ElevenI_1283
      · exact prime_free64ElevenI_143419
      · exact prime_free64ElevenI_1102237441693
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

private theorem prime_free64ElevenI_189677329 : Nat.Prime 189677329 := by
  have hfermat : (33 : ZMod 189677329) ^ (189677329 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (33 : ZMod 189677329) ^ ((189677329 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (33 : ZMod 189677329) ^ ((189677329 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (33 : ZMod 189677329) ^ ((189677329 - 1) / 3951611) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 189677329 (33 : ZMod 189677329)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (3, 1), (3951611, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (3, 1), (3951611, 1)] : List FactorBlock).map factorBlockValue).prod = 189677329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_3951611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_9156358179653 : Nat.Prime 9156358179653 := by
  have hfermat : (2 : ZMod 9156358179653) ^ (9156358179653 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 9156358179653) ^ ((9156358179653 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 9156358179653) ^ ((9156358179653 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 9156358179653) ^ ((9156358179653 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 9156358179653) ^ ((9156358179653 - 1) / 647) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 9156358179653) ^ ((9156358179653 - 1) / 1009993) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 9156358179653 (2 : ZMod 9156358179653)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (31, 1), (113, 1), (647, 1), (1009993, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (31, 1), (113, 1), (647, 1), (1009993, 1)] : List FactorBlock).map factorBlockValue).prod = 9156358179653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_t64_113
      · exact prime_t64_647
      · exact prime_free64ElevenI_1009993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_187569384791459384178397 : Nat.Prime 187569384791459384178397 := by
  have hfermat : (2 : ZMod 187569384791459384178397) ^ (187569384791459384178397 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 187569384791459384178397) ^ ((187569384791459384178397 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 187569384791459384178397) ^ ((187569384791459384178397 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 187569384791459384178397) ^ ((187569384791459384178397 - 1) / 189677329) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 187569384791459384178397) ^ ((187569384791459384178397 - 1) / 9156358179653) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 187569384791459384178397 (2 : ZMod 187569384791459384178397)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (189677329, 1), (9156358179653, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (189677329, 1), (9156358179653, 1)] : List FactorBlock).map factorBlockValue).prod = 187569384791459384178397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_189677329
      · exact prime_free64ElevenI_9156358179653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_53504597 : Nat.Prime 53504597 := by
  have hfermat : (2 : ZMod 53504597) ^ (53504597 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 53504597) ^ ((53504597 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 53504597) ^ ((53504597 - 1) / 113) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 53504597) ^ ((53504597 - 1) / 118373) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 53504597 (2 : ZMod 53504597)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (113, 1), (118373, 1)] : List FactorBlock).map factorBlockValue).prod = 53504597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_113
      · exact prime_free64ElevenI_118373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_403073885242069 : Nat.Prime 403073885242069 := by
  have hfermat : (2 : ZMod 403073885242069) ^ (403073885242069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 403073885242069) ^ ((403073885242069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 403073885242069) ^ ((403073885242069 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 403073885242069) ^ ((403073885242069 - 1) / 627787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 403073885242069) ^ ((403073885242069 - 1) / 53504597) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 403073885242069 (2 : ZMod 403073885242069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (627787, 1), (53504597, 1)] : List FactorBlock).map factorBlockValue).prod = 403073885242069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_627787
      · exact prime_free64ElevenI_53504597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_611866157797460743 : Nat.Prime 611866157797460743 := by
  have hfermat : (5 : ZMod 611866157797460743) ^ (611866157797460743 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 611866157797460743) ^ ((611866157797460743 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 611866157797460743) ^ ((611866157797460743 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 611866157797460743) ^ ((611866157797460743 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 611866157797460743) ^ ((611866157797460743 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 611866157797460743) ^ ((611866157797460743 - 1) / 403073885242069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 611866157797460743 (5 : ZMod 611866157797460743)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (23, 1), (403073885242069, 1)] : List FactorBlock).map factorBlockValue).prod = 611866157797460743 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_23
      · exact prime_free64ElevenI_403073885242069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_262688826330237036027733 : Nat.Prime 262688826330237036027733 := by
  have hfermat : (5 : ZMod 262688826330237036027733) ^ (262688826330237036027733 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 269) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (5 : ZMod 262688826330237036027733) ^ ((262688826330237036027733 - 1) / 611866157797460743) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 262688826330237036027733 (5 : ZMod 262688826330237036027733)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (7, 1), (19, 1), (269, 1), (611866157797460743, 1)] : List FactorBlock).map factorBlockValue).prod = 262688826330237036027733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_19
      · exact prime_t64_269
      · exact prime_free64ElevenI_611866157797460743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_66486181 : Nat.Prime 66486181 := by
  have hfermat : (6 : ZMod 66486181) ^ (66486181 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 66486181) ^ ((66486181 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 66486181) ^ ((66486181 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 66486181) ^ ((66486181 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 66486181) ^ ((66486181 - 1) / 1108103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 66486181 (6 : ZMod 66486181)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (5, 1), (1108103, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (5, 1), (1108103, 1)] : List FactorBlock).map factorBlockValue).prod = 66486181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_1108103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_1861613069 : Nat.Prime 1861613069 := by
  have hfermat : (2 : ZMod 1861613069) ^ (1861613069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 1861613069) ^ ((1861613069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 1861613069) ^ ((1861613069 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 1861613069) ^ ((1861613069 - 1) / 66486181) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1861613069 (2 : ZMod 1861613069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (7, 1), (66486181, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (7, 1), (66486181, 1)] : List FactorBlock).map factorBlockValue).prod = 1861613069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_free64ElevenI_66486181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1247228631064069 : Nat.Prime 1247228631064069 := by
  have hfermat : (6 : ZMod 1247228631064069) ^ (1247228631064069 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1247228631064069) ^ ((1247228631064069 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1247228631064069) ^ ((1247228631064069 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1247228631064069) ^ ((1247228631064069 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1247228631064069) ^ ((1247228631064069 - 1) / 1801) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1247228631064069) ^ ((1247228631064069 - 1) / 1861613069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1247228631064069 (6 : ZMod 1247228631064069)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (31, 1), (1801, 1), (1861613069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (31, 1), (1801, 1), (1861613069, 1)] : List FactorBlock).map factorBlockValue).prod = 1247228631064069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_31
      · exact prime_t64_1801
      · exact prime_free64ElevenI_1861613069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_352609287054146872258147 : Nat.Prime 352609287054146872258147 := by
  have hfermat : (2 : ZMod 352609287054146872258147) ^ (352609287054146872258147 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 138179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 352609287054146872258147) ^ ((352609287054146872258147 - 1) / 1247228631064069) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 352609287054146872258147 (2 : ZMod 352609287054146872258147)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 1), (31, 1), (138179, 1), (1247228631064069, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 1), (31, 1), (138179, 1), (1247228631064069, 1)] : List FactorBlock).map factorBlockValue).prod = 352609287054146872258147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_31
      · exact prime_free64ElevenI_138179
      · exact prime_free64ElevenI_1247228631064069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_29304298123 : Nat.Prime 29304298123 := by
  have hfermat : (2 : ZMod 29304298123) ^ (29304298123 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 29304298123) ^ ((29304298123 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 29304298123) ^ ((29304298123 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 29304298123) ^ ((29304298123 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 29304298123) ^ ((29304298123 - 1) / 1229) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 29304298123) ^ ((29304298123 - 1) / 32843) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 29304298123 (2 : ZMod 29304298123)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (11, 2), (1229, 1), (32843, 1)] : List FactorBlock).map factorBlockValue).prod = 29304298123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_11
      · exact prime_t64_1229
      · exact prime_free64ElevenI_32843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_98695889 : Nat.Prime 98695889 := by
  have hfermat : (3 : ZMod 98695889) ^ (98695889 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 98695889) ^ ((98695889 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 98695889) ^ ((98695889 - 1) / 967) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 98695889) ^ ((98695889 - 1) / 6379) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 98695889 (3 : ZMod 98695889)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (967, 1), (6379, 1)] : List FactorBlock).map factorBlockValue).prod = 98695889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_967
      · exact prime_free64ElevenI_6379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_3496992739049 : Nat.Prime 3496992739049 := by
  have hfermat : (3 : ZMod 3496992739049) ^ (3496992739049 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3496992739049) ^ ((3496992739049 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3496992739049) ^ ((3496992739049 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3496992739049) ^ ((3496992739049 - 1) / 103) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 3496992739049) ^ ((3496992739049 - 1) / 98695889) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3496992739049 (3 : ZMod 3496992739049)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (43, 1), (103, 1), (98695889, 1)] : List FactorBlock).map factorBlockValue).prod = 3496992739049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_43
      · exact prime_t64_103
      · exact prime_free64ElevenI_98695889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_614861506554349437030163 : Nat.Prime 614861506554349437030163 := by
  have hfermat : (3 : ZMod 614861506554349437030163) ^ (614861506554349437030163 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 614861506554349437030163) ^ ((614861506554349437030163 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 614861506554349437030163) ^ ((614861506554349437030163 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 614861506554349437030163) ^ ((614861506554349437030163 - 1) / 29304298123) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 614861506554349437030163) ^ ((614861506554349437030163 - 1) / 3496992739049) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 614861506554349437030163 (3 : ZMod 614861506554349437030163)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (29304298123, 1), (3496992739049, 1)] : List FactorBlock).map factorBlockValue).prod = 614861506554349437030163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_29304298123
      · exact prime_free64ElevenI_3496992739049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_140770891 : Nat.Prime 140770891 := by
  have hfermat : (2 : ZMod 140770891) ^ (140770891 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 79) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 140770891) ^ ((140770891 - 1) / 1523) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 140770891 (2 : ZMod 140770891)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (13, 1), (79, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (13, 1), (79, 1), (1523, 1)] : List FactorBlock).map factorBlockValue).prod = 140770891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_13
      · exact prime_t64_79
      · exact prime_free64ElevenI_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_2533876039 : Nat.Prime 2533876039 := by
  have hfermat : (6 : ZMod 2533876039) ^ (2533876039 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 2533876039) ^ ((2533876039 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 2533876039) ^ ((2533876039 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 2533876039) ^ ((2533876039 - 1) / 140770891) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2533876039 (6 : ZMod 2533876039)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (140770891, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (140770891, 1)] : List FactorBlock).map factorBlockValue).prod = 2533876039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_140770891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_42143426280649 : Nat.Prime 42143426280649 := by
  have hfermat : (13 : ZMod 42143426280649) ^ (42143426280649 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 42143426280649) ^ ((42143426280649 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 42143426280649) ^ ((42143426280649 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 42143426280649) ^ ((42143426280649 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 42143426280649) ^ ((42143426280649 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 42143426280649) ^ ((42143426280649 - 1) / 2533876039) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 42143426280649 (13 : ZMod 42143426280649)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (7, 1), (11, 1), (2533876039, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (7, 1), (11, 1), (2533876039, 1)] : List FactorBlock).map factorBlockValue).prod = 42143426280649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64ElevenI_2533876039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_1190165253512496105301087 : Nat.Prime 1190165253512496105301087 := by
  have hfermat : (3 : ZMod 1190165253512496105301087) ^ (1190165253512496105301087 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 641) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 28351) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 1190165253512496105301087) ^ ((1190165253512496105301087 - 1) / 42143426280649) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1190165253512496105301087 (3 : ZMod 1190165253512496105301087)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (7, 1), (37, 1), (641, 1), (28351, 1), (42143426280649, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (7, 1), (37, 1), (641, 1), (28351, 1), (42143426280649, 1)] : List FactorBlock).map factorBlockValue).prod = 1190165253512496105301087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_7
      · exact prime_t64_37
      · exact prime_t64_641
      · exact prime_free64ElevenI_28351
      · exact prime_free64ElevenI_42143426280649
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

private theorem prime_free64ElevenI_11503777 : Nat.Prime 11503777 := by
  have hfermat : (5 : ZMod 11503777) ^ (11503777 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 11503777) ^ ((11503777 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 11503777) ^ ((11503777 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 11503777) ^ ((11503777 - 1) / 119831) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 11503777 (5 : ZMod 11503777)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (119831, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (119831, 1)] : List FactorBlock).map factorBlockValue).prod = 11503777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_free64ElevenI_119831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_30492110377557209 : Nat.Prime 30492110377557209 := by
  have hfermat : (3 : ZMod 30492110377557209) ^ (30492110377557209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 30492110377557209) ^ ((30492110377557209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 30492110377557209) ^ ((30492110377557209 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 30492110377557209) ^ ((30492110377557209 - 1) / 1637) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 30492110377557209) ^ ((30492110377557209 - 1) / 6529) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 30492110377557209) ^ ((30492110377557209 - 1) / 11503777) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 30492110377557209 (3 : ZMod 30492110377557209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (31, 1), (1637, 1), (6529, 1), (11503777, 1)] : List FactorBlock).map factorBlockValue).prod = 30492110377557209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_31
      · exact prime_free64ElevenI_1637
      · exact prime_free64ElevenI_6529
      · exact prime_free64ElevenI_11503777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_28418646871883318789 : Nat.Prime 28418646871883318789 := by
  have hfermat : (2 : ZMod 28418646871883318789) ^ (28418646871883318789 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 28418646871883318789) ^ ((28418646871883318789 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 28418646871883318789) ^ ((28418646871883318789 - 1) / 233) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 28418646871883318789) ^ ((28418646871883318789 - 1) / 30492110377557209) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 28418646871883318789 (2 : ZMod 28418646871883318789)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (233, 1), (30492110377557209, 1)] : List FactorBlock).map factorBlockValue).prod = 28418646871883318789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_233
      · exact prime_free64ElevenI_30492110377557209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_2554495330019847759305633 : Nat.Prime 2554495330019847759305633 := by
  have hfermat : (3 : ZMod 2554495330019847759305633) ^ (2554495330019847759305633 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2554495330019847759305633) ^ ((2554495330019847759305633 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2554495330019847759305633) ^ ((2554495330019847759305633 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2554495330019847759305633) ^ ((2554495330019847759305633 - 1) / 28418646871883318789) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2554495330019847759305633 (3 : ZMod 2554495330019847759305633)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (53, 2), (28418646871883318789, 1)] : List FactorBlock).map factorBlockValue).prod = 2554495330019847759305633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_53
      · exact prime_free64ElevenI_28418646871883318789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_18918168251 : Nat.Prime 18918168251 := by
  have hfermat : (2 : ZMod 18918168251) ^ (18918168251 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 18918168251) ^ ((18918168251 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 18918168251) ^ ((18918168251 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 18918168251) ^ ((18918168251 - 1) / 7867) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 18918168251) ^ ((18918168251 - 1) / 9619) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 18918168251 (2 : ZMod 18918168251)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 3), (7867, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 3), (7867, 1), (9619, 1)] : List FactorBlock).map factorBlockValue).prod = 18918168251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_free64ElevenI_7867
      · exact prime_free64ElevenI_9619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_36097547755948408265491 : Nat.Prime 36097547755948408265491 := by
  have hfermat : (3 : ZMod 36097547755948408265491) ^ (36097547755948408265491 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 29131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 727781) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 36097547755948408265491) ^ ((36097547755948408265491 - 1) / 18918168251) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 36097547755948408265491 (3 : ZMod 36097547755948408265491)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (29131, 1), (727781, 1), (18918168251, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (29131, 1), (727781, 1), (18918168251, 1)] : List FactorBlock).map factorBlockValue).prod = 36097547755948408265491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_29131
      · exact prime_free64ElevenI_727781
      · exact prime_free64ElevenI_18918168251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_3176584202523459927363209 : Nat.Prime 3176584202523459927363209 := by
  have hfermat : (3 : ZMod 3176584202523459927363209) ^ (3176584202523459927363209 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 3176584202523459927363209) ^ ((3176584202523459927363209 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 3176584202523459927363209) ^ ((3176584202523459927363209 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 3176584202523459927363209) ^ ((3176584202523459927363209 - 1) / 36097547755948408265491) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 3176584202523459927363209 (3 : ZMod 3176584202523459927363209)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (11, 1), (36097547755948408265491, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (11, 1), (36097547755948408265491, 1)] : List FactorBlock).map factorBlockValue).prod = 3176584202523459927363209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_11
      · exact prime_free64ElevenI_36097547755948408265491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_7088013991 : Nat.Prime 7088013991 := by
  have hfermat : (11 : ZMod 7088013991) ^ (7088013991 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 151) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (11 : ZMod 7088013991) ^ ((7088013991 - 1) / 12721) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 7088013991 (11 : ZMod 7088013991)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 2), (5, 1), (41, 1), (151, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod = 7088013991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_41
      · exact prime_free64ElevenI_151
      · exact prime_free64ElevenI_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_974357259695558663 : Nat.Prime 974357259695558663 := by
  have hfermat : (5 : ZMod 974357259695558663) ^ (974357259695558663 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (5 : ZMod 974357259695558663) ^ ((974357259695558663 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (5 : ZMod 974357259695558663) ^ ((974357259695558663 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (5 : ZMod 974357259695558663) ^ ((974357259695558663 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (5 : ZMod 974357259695558663) ^ ((974357259695558663 - 1) / 18217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (5 : ZMod 974357259695558663) ^ ((974357259695558663 - 1) / 7088013991) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 974357259695558663 (5 : ZMod 974357259695558663)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (7, 3), (11, 1), (18217, 1), (7088013991, 1)] : List FactorBlock).map factorBlockValue).prod = 974357259695558663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_7
      · exact prime_t64_11
      · exact prime_free64ElevenI_18217
      · exact prime_free64ElevenI_7088013991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_5698920124947872455138027 : Nat.Prime 5698920124947872455138027 := by
  have hfermat : (2 : ZMod 5698920124947872455138027) ^ (5698920124947872455138027 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 5698920124947872455138027) ^ ((5698920124947872455138027 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 5698920124947872455138027) ^ ((5698920124947872455138027 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 5698920124947872455138027) ^ ((5698920124947872455138027 - 1) / 89) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 5698920124947872455138027) ^ ((5698920124947872455138027 - 1) / 1217) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 5698920124947872455138027) ^ ((5698920124947872455138027 - 1) / 974357259695558663) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 5698920124947872455138027 (2 : ZMod 5698920124947872455138027)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (89, 1), (1217, 1), (974357259695558663, 1)] : List FactorBlock).map factorBlockValue).prod = 5698920124947872455138027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_89
      · exact prime_free64ElevenI_1217
      · exact prime_free64ElevenI_974357259695558663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_16259179 : Nat.Prime 16259179 := by
  have hfermat : (2 : ZMod 16259179) ^ (16259179 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 16259179) ^ ((16259179 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 16259179) ^ ((16259179 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 16259179) ^ ((16259179 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 16259179) ^ ((16259179 - 1) / 149) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 16259179) ^ ((16259179 - 1) / 1399) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16259179 (2 : ZMod 16259179)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (149, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (149, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod = 16259179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_t64_149
      · exact prime_free64ElevenI_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_487775371 : Nat.Prime 487775371 := by
  have hfermat : (2 : ZMod 487775371) ^ (487775371 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 487775371) ^ ((487775371 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 487775371) ^ ((487775371 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 487775371) ^ ((487775371 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 487775371) ^ ((487775371 - 1) / 16259179) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 487775371 (2 : ZMod 487775371)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (16259179, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (16259179, 1)] : List FactorBlock).map factorBlockValue).prod = 487775371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_16259179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_2723357768791847393 : Nat.Prime 2723357768791847393 := by
  have hfermat : (3 : ZMod 2723357768791847393) ^ (2723357768791847393 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 2723357768791847393) ^ ((2723357768791847393 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 2723357768791847393) ^ ((2723357768791847393 - 1) / 5471) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 2723357768791847393) ^ ((2723357768791847393 - 1) / 31891) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 2723357768791847393) ^ ((2723357768791847393 - 1) / 487775371) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 2723357768791847393 (3 : ZMod 2723357768791847393)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (5471, 1), (31891, 1), (487775371, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (5471, 1), (31891, 1), (487775371, 1)] : List FactorBlock).map factorBlockValue).prod = 2723357768791847393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_5471
      · exact prime_free64ElevenI_31891
      · exact prime_free64ElevenI_487775371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_6784004029802318697248293 : Nat.Prime 6784004029802318697248293 := by
  have hfermat : (2 : ZMod 6784004029802318697248293) ^ (6784004029802318697248293 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 6784004029802318697248293) ^ ((6784004029802318697248293 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 6784004029802318697248293) ^ ((6784004029802318697248293 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 6784004029802318697248293) ^ ((6784004029802318697248293 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 6784004029802318697248293) ^ ((6784004029802318697248293 - 1) / 12211) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 6784004029802318697248293) ^ ((6784004029802318697248293 - 1) / 2723357768791847393) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 6784004029802318697248293 (2 : ZMod 6784004029802318697248293)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 1), (17, 1), (12211, 1), (2723357768791847393, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 1), (17, 1), (12211, 1), (2723357768791847393, 1)] : List FactorBlock).map factorBlockValue).prod = 6784004029802318697248293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_17
      · exact prime_free64ElevenI_12211
      · exact prime_free64ElevenI_2723357768791847393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_16559009 : Nat.Prime 16559009 := by
  have hfermat : (3 : ZMod 16559009) ^ (16559009 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 16559009) ^ ((16559009 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 16559009) ^ ((16559009 - 1) / 517469) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 16559009 (3 : ZMod 16559009)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (517469, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (517469, 1)] : List FactorBlock).map factorBlockValue).prod = 16559009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_517469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfactor_0
    · exact hfactor_1

private theorem prime_free64ElevenI_99365011 : Nat.Prime 99365011 := by
  have hfermat : (2 : ZMod 99365011) ^ (99365011 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 99365011) ^ ((99365011 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 99365011) ^ ((99365011 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 99365011) ^ ((99365011 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 99365011) ^ ((99365011 - 1) / 3312167) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 99365011 (2 : ZMod 99365011)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (5, 1), (3312167, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (5, 1), (3312167, 1)] : List FactorBlock).map factorBlockValue).prod = 99365011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_free64ElevenI_3312167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem prime_free64ElevenI_284886131 : Nat.Prime 284886131 := by
  have hfermat : (2 : ZMod 284886131) ^ (284886131 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 284886131) ^ ((284886131 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 284886131) ^ ((284886131 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 284886131) ^ ((284886131 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 284886131) ^ ((284886131 - 1) / 683) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 284886131) ^ ((284886131 - 1) / 787) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 284886131 (2 : ZMod 284886131)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (53, 1), (683, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (53, 1), (683, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod = 284886131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_53
      · exact prime_t64_683
      · exact prime_t64_787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_56615427081124883 : Nat.Prime 56615427081124883 := by
  have hfermat : (2 : ZMod 56615427081124883) ^ (56615427081124883 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 56615427081124883) ^ ((56615427081124883 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 56615427081124883) ^ ((56615427081124883 - 1) / 99365011) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 56615427081124883) ^ ((56615427081124883 - 1) / 284886131) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 56615427081124883 (2 : ZMod 56615427081124883)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (99365011, 1), (284886131, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (99365011, 1), (284886131, 1)] : List FactorBlock).map factorBlockValue).prod = 56615427081124883 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_99365011
      · exact prime_free64ElevenI_284886131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_14999925865203050683535153 : Nat.Prime 14999925865203050683535153 := by
  have hfermat : (3 : ZMod 14999925865203050683535153) ^ (14999925865203050683535153 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 14999925865203050683535153) ^ ((14999925865203050683535153 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 14999925865203050683535153) ^ ((14999925865203050683535153 - 1) / 16559009) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 14999925865203050683535153) ^ ((14999925865203050683535153 - 1) / 56615427081124883) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 14999925865203050683535153 (3 : ZMod 14999925865203050683535153)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 4), (16559009, 1), (56615427081124883, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 4), (16559009, 1), (56615427081124883, 1)] : List FactorBlock).map factorBlockValue).prod = 14999925865203050683535153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_free64ElevenI_16559009
      · exact prime_free64ElevenI_56615427081124883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2

private theorem prime_free64ElevenI_1304698691 : Nat.Prime 1304698691 := by
  have hfermat : (6 : ZMod 1304698691) ^ (1304698691 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 1304698691) ^ ((1304698691 - 1) / 4549) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 1304698691 (6 : ZMod 1304698691)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (5, 1), (23, 1), (29, 1), (43, 1), (4549, 1)] : List FactorBlock).map factorBlockValue).prod = 1304698691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_5
      · exact prime_t64_23
      · exact prime_t64_29
      · exact prime_t64_43
      · exact prime_free64ElevenI_4549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_4049080921 : Nat.Prime 4049080921 := by
  have hfermat : (11 : ZMod 4049080921) ^ (4049080921 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (11 : ZMod 4049080921) ^ ((4049080921 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (11 : ZMod 4049080921) ^ ((4049080921 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (11 : ZMod 4049080921) ^ ((4049080921 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (11 : ZMod 4049080921) ^ ((4049080921 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (11 : ZMod 4049080921) ^ ((4049080921 - 1) / 129281) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 4049080921 (11 : ZMod 4049080921)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 3), (3, 3), (5, 1), (29, 1), (129281, 1)] : List FactorBlock).map factorBlockValue).prod = 4049080921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_5
      · exact prime_t64_29
      · exact prime_free64ElevenI_129281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4

private theorem prime_free64ElevenI_160554762038654875834876267 : Nat.Prime 160554762038654875834876267 := by
  have hfermat : (2 : ZMod 160554762038654875834876267) ^ (160554762038654875834876267 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 137) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 36973) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 1304698691) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (2 : ZMod 160554762038654875834876267) ^ ((160554762038654875834876267 - 1) / 4049080921) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 160554762038654875834876267 (2 : ZMod 160554762038654875834876267)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (137, 1), (36973, 1), (1304698691, 1), (4049080921, 1)] : List FactorBlock).map factorBlockValue).prod = 160554762038654875834876267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_137
      · exact prime_free64ElevenI_36973
      · exact prime_free64ElevenI_1304698691
      · exact prime_free64ElevenI_4049080921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3
    · exact hfactor_4
    · exact hfactor_5

private theorem prime_free64ElevenI_162561696564138061782812221 : Nat.Prime 162561696564138061782812221 := by
  have hfermat : (6 : ZMod 162561696564138061782812221) ^ (162561696564138061782812221 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (6 : ZMod 162561696564138061782812221) ^ ((162561696564138061782812221 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 162561696564138061782812221 (6 : ZMod 162561696564138061782812221)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 2), (3, 3), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 2), (3, 3), (5, 1), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 162561696564138061782812221 - 1 by
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

private theorem prime_free64ElevenI_166729945193987755674679201 : Nat.Prime 166729945193987755674679201 := by
  have hfermat : (13 : ZMod 166729945193987755674679201) ^ (166729945193987755674679201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (13 : ZMod 166729945193987755674679201) ^ ((166729945193987755674679201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 166729945193987755674679201 (13 : ZMod 166729945193987755674679201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 2), (5, 2), (7, 2), (11, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 2), (5, 2), (7, 2), (11, 2), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 166729945193987755674679201 - 1 by
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

private theorem prime_free64ElevenI_245376145757189527219339201 : Nat.Prime 245376145757189527219339201 := by
  have hfermat : (146 : ZMod 245376145757189527219339201) ^ (245376145757189527219339201 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (146 : ZMod 245376145757189527219339201) ^ ((245376145757189527219339201 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 245376145757189527219339201 (146 : ZMod 245376145757189527219339201)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 245376145757189527219339201 - 1 by
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
      · exact prime_t64_41
      · exact prime_t64_43
      · exact prime_t64_47
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

private theorem prime_free64ElevenI_351484749327866079530404801 : Nat.Prime 351484749327866079530404801 := by
  have hfermat : (89 : ZMod 351484749327866079530404801) ^ (351484749327866079530404801 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (89 : ZMod 351484749327866079530404801) ^ ((351484749327866079530404801 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 351484749327866079530404801 (89 : ZMod 351484749327866079530404801)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 351484749327866079530404801 - 1 by
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

private theorem prime_free64ElevenI_406404241410345154457030551 : Nat.Prime 406404241410345154457030551 := by
  have hfermat : (3 : ZMod 406404241410345154457030551) ^ (406404241410345154457030551 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 5) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 7) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_4 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 11) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_5 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_6 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 17) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_7 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 19) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_8 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 23) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_9 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 29) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_10 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 31) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_11 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 37) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_12 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 41) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_13 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 43) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_14 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 47) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_15 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 53) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_16 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 59) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_17 : (3 : ZMod 406404241410345154457030551) ^ ((406404241410345154457030551 - 1) / 61) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 406404241410345154457030551 (3 : ZMod 406404241410345154457030551)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod = 406404241410345154457030551 - 1 by
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

private theorem prime_free64ElevenI_13004935725131044942624977679 : Nat.Prime 13004935725131044942624977679 := by
  have hfermat : (6 : ZMod 13004935725131044942624977679) ^ (13004935725131044942624977679 - 1) = 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_eq_one_iff]
    decide +kernel
  have hfactor_0 : (6 : ZMod 13004935725131044942624977679) ^ ((13004935725131044942624977679 - 1) / 2) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_1 : (6 : ZMod 13004935725131044942624977679) ^ ((13004935725131044942624977679 - 1) / 3) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_2 : (6 : ZMod 13004935725131044942624977679) ^ ((13004935725131044942624977679 - 1) / 13) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  have hfactor_3 : (6 : ZMod 13004935725131044942624977679) ^ ((13004935725131044942624977679 - 1) / 166729945193987755674679201) ≠ 1 := by
    rw [← binaryPow_eq_pow, binaryPow_zmod, natCast_zmod_ne_one_iff]
    decide +kernel
  apply lucas_primality 13004935725131044942624977679 (6 : ZMod 13004935725131044942624977679)
  · exact hfermat
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 1), (3, 1), (13, 1), (166729945193987755674679201, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 1), (3, 1), (13, 1), (166729945193987755674679201, 1)] : List FactorBlock).map factorBlockValue).prod = 13004935725131044942624977679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_t64_2
      · exact prime_t64_3
      · exact prime_t64_13
      · exact prime_free64ElevenI_166729945193987755674679201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hfactor_0
    · exact hfactor_1
    · exact hfactor_2
    · exact hfactor_3

private theorem phi_free64ElevenI_13004935725131044942624977597 :
    Nat.totient 13004935725131044942624977597 = 8667828439281178624416960000 := by
  rw [← show
    ((([(3, 1), (4159, 1), (230281, 1), (1344901, 1), (3365500130981, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977597 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64ElevenI_4159, prime_free64ElevenI_230281, prime_free64ElevenI_1344901, prime_free64ElevenI_3365500130981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977598 :
    Nat.totient 13004935725131044942624977598 = 6502280293180731011928275736 := by
  rw [← show
    ((([(2, 1), (34667, 1), (187569384791459384178397, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977598 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_34667, prime_free64ElevenI_187569384791459384178397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977599 :
    Nat.totient 13004935725131044942624977599 = 13004923904883095479279785280 := by
  rw [← show
    ((([(1101371, 1), (1057745573, 1), (11163319554953, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977599 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_1101371, prime_free64ElevenI_1057745573, prime_free64ElevenI_11163319554953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977600 :
    Nat.totient 13004935725131044942624977600 = 1711285053052967033241600000 := by
  rw [← show
    ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 2), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977600 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_7, prime_t64_11, prime_t64_13, prime_t64_17, prime_t64_19, prime_t64_23, prime_t64_29, prime_t64_31, prime_t64_37, prime_t64_41, prime_t64_43, prime_t64_47, prime_t64_53, prime_t64_59, prime_t64_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977601 :
    Nat.totient 13004935725131044942624977601 = 12848235399057265116828962560 := by
  rw [← show
    ((([(83, 1), (895529, 1), (2064319931, 1), (84756586553, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977601 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_83, prime_free64ElevenI_895529, prime_free64ElevenI_2064319931, prime_free64ElevenI_84756586553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977602 :
    Nat.totient 13004935725131044942624977602 = 6502467282356313489693911472 := by
  rw [← show
    ((([(2, 1), (11218483, 1), (15837208853, 1), (36598681199, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977602 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_11218483, prime_free64ElevenI_15837208853, prime_free64ElevenI_36598681199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977603 :
    Nat.totient 13004935725131044942624977603 = 8664848159427323599564703744 := by
  rw [← show
    ((([(3, 1), (1697, 1), (2554495330019847759305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977603 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64ElevenI_1697, prime_free64ElevenI_2554495330019847759305633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977604 :
    Nat.totient 13004935725131044942624977604 = 6500923613616235295285357280 := by
  rw [← show
    ((([(2, 2), (4211, 1), (75111599, 1), (10279120799235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977604 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_4211, prime_free64ElevenI_75111599, prime_free64ElevenI_10279120799235109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977605 :
    Nat.totient 13004935725131044942624977605 = 10378662057655325895374726400 := by
  rw [← show
    ((([(5, 1), (631, 1), (1181, 1), (3446959, 1), (1012564812501629, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977605 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64ElevenI_631, prime_free64ElevenI_1181, prime_free64ElevenI_3446959, prime_free64ElevenI_1012564812501629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977606 :
    Nat.totient 13004935725131044942624977606 = 4334978574294927998204841984 := by
  rw [← show
    ((([(2, 1), (3, 1), (5789592673, 1), (374376818878815937, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977606 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_5789592673, prime_free64ElevenI_374376818878815937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977607 :
    Nat.totient 13004935725131044942624977607 = 11146745103927582709685700600 := by
  rw [← show
    ((([(7, 1), (32531, 1), (57110078409302094014171, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977607 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_free64ElevenI_32531, prime_free64ElevenI_57110078409302094014171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977608 :
    Nat.totient 13004935725131044942624977608 = 6494682786514532806689833472 := by
  rw [← show
    ((([(2, 3), (857, 1), (32869, 1), (57709978139285874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977608 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_857, prime_free64ElevenI_32869, prime_free64ElevenI_57709978139285874797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977609 :
    Nat.totient 13004935725131044942624977609 = 8584115657778454378661222400 := by
  rw [← show
    ((([(3, 2), (101, 1), (25824109, 1), (554011756364663489, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977609 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_101, prime_free64ElevenI_25824109, prime_free64ElevenI_554011756364663489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977610 :
    Nat.totient 13004935725131044942624977610 = 5128564121507578540720673280 := by
  rw [← show
    ((([(2, 1), (5, 1), (71, 1), (37967, 1), (834527, 1), (3072847, 1), (188131817, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977610 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_71, prime_free64ElevenI_37967, prime_free64ElevenI_834527, prime_free64ElevenI_3072847, prime_free64ElevenI_188131817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977611 :
    Nat.totient 13004935725131044942624977611 = 11705548278532956395009761920 := by
  rw [← show
    ((([(11, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977611 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977612 :
    Nat.totient 13004935725131044942624977612 = 4314681159884373637366075392 := by
  rw [← show
    ((([(2, 2), (3, 1), (257, 1), (1259, 1), (3349408442130034682227, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977612 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_257, prime_free64ElevenI_1259, prime_free64ElevenI_3349408442130034682227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977613 :
    Nat.totient 13004935725131044942624977613 = 11997177715888466215332520944 := by
  rw [← show
    ((([(13, 1), (1627, 1), (614861506554349437030163, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977613 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_free64ElevenI_1627, prime_free64ElevenI_614861506554349437030163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977614 :
    Nat.totient 13004935725131044942624977614 = 5539350361449332026394161272 := by
  rw [← show
    ((([(2, 1), (7, 1), (163, 1), (5698920124947872455138027, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977614 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_163, prime_free64ElevenI_5698920124947872455138027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977615 :
    Nat.totient 13004935725131044942624977615 = 6934160660621173445213927424 := by
  rw [← show
    ((([(3, 1), (5, 1), (4493, 1), (31159, 1), (222419, 1), (940573, 1), (29602789, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977615 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64ElevenI_4493, prime_free64ElevenI_31159, prime_free64ElevenI_222419, prime_free64ElevenI_940573, prime_free64ElevenI_29602789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977616 :
    Nat.totient 13004935725131044942624977616 = 6370027064177323901970084480 := by
  rw [← show
    ((([(2, 4), (67, 1), (181, 1), (67024695540586320517363, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977616 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_67, prime_free64ElevenI_181, prime_free64ElevenI_67024695540586320517363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977617 :
    Nat.totient 13004935725131044942624977617 = 12239939492248792397892164352 := by
  rw [← show
    ((([(17, 1), (889731133, 1), (859806059102301397, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977617 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_free64ElevenI_889731133, prime_free64ElevenI_859806059102301397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977618 :
    Nat.totient 13004935725131044942624977618 = 4334914270882153132534936800 := by
  rw [← show
    ((([(2, 1), (3, 2), (67901, 1), (9392503, 1), (1132865085569267, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977618 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_67901, prime_free64ElevenI_9392503, prime_free64ElevenI_1132865085569267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977619 :
    Nat.totient 13004935725131044942624977619 = 12250202219670793464078336000 := by
  rw [← show
    ((([(19, 1), (241, 1), (641, 1), (4430773372276762682321, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977619 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_free64ElevenI_241, prime_t64_641, prime_free64ElevenI_4430773372276762682321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977620 :
    Nat.totient 13004935725131044942624977620 = 5182631501052668679076623360 := by
  rw [← show
    ((([(2, 2), (5, 1), (269, 1), (1127981, 1), (2143009765547021929, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977620 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_269, prime_free64ElevenI_1127981, prime_free64ElevenI_2143009765547021929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977621 :
    Nat.totient 13004935725131044942624977621 = 7384058134333903213780155840 := by
  rw [← show
    ((([(3, 1), (7, 1), (157, 1), (2848589311, 1), (1384711894151563, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977621 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_157, prime_free64ElevenI_2848589311, prime_free64ElevenI_1384711894151563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977622 :
    Nat.totient 13004935725131044942624977622 = 5911334415679122453822061000 := by
  rw [← show
    ((([(2, 1), (11, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977622 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977623 :
    Nat.totient 13004935725131044942624977623 = 12427888913613301365238510080 := by
  rw [← show
    ((([(23, 1), (1307, 1), (5927, 1), (289278289, 1), (252321361381, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977623 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_free64ElevenI_1307, prime_free64ElevenI_5927, prime_free64ElevenI_289278289, prime_free64ElevenI_252321361381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977624 :
    Nat.totient 13004935725131044942624977624 = 4334977687763136266371911200 := by
  rw [← show
    ((([(2, 3), (3, 1), (4885691, 1), (110910068172641332811, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977624 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_4885691, prime_free64ElevenI_110910068172641332811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977625 :
    Nat.totient 13004935725131044942624977625 = 10403944713069279782454072000 := by
  rw [← show
    ((([(5, 3), (2719511, 1), (251922637, 1), (151858876903, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977625 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_free64ElevenI_2719511, prime_free64ElevenI_251922637, prime_free64ElevenI_151858876903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977626 :
    Nat.totient 13004935725131044942624977626 = 6001650380404779412613938560 := by
  rw [← show
    ((([(2, 1), (13, 1), (12227, 1), (43891, 1), (932050565158189193, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977626 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_free64ElevenI_12227, prime_free64ElevenI_43891, prime_free64ElevenI_932050565158189193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977627 :
    Nat.totient 13004935725131044942624977627 = 8669957150087363295083318364 := by
  rw [← show
    ((([(3, 4), (160554762038654875834876267, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977627 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_free64ElevenI_160554762038654875834876267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977628 :
    Nat.totient 13004935725131044942624977628 = 5573543879056954549232026800 := by
  rw [← show
    ((([(2, 2), (7, 1), (1773847591, 1), (261838724217232711, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977628 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64ElevenI_1773847591, prime_free64ElevenI_261838724217232711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977629 :
    Nat.totient 13004935725131044942624977629 = 12556455383309608475870760000 := by
  rw [← show
    ((([(29, 1), (432391, 1), (2395051, 1), (433030813401061, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977629 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_free64ElevenI_432391, prime_free64ElevenI_2395051, prime_free64ElevenI_433030813401061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977630 :
    Nat.totient 13004935725131044942624977630 = 3442138609267317699908812800 := by
  rw [← show
    ((([(2, 1), (3, 1), (5, 1), (149, 1), (2161, 1), (4457, 1), (16987, 1), (17782245395071, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977630 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_149, prime_free64ElevenI_2161, prime_free64ElevenI_4457, prime_free64ElevenI_16987, prime_free64ElevenI_17782245395071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977631 :
    Nat.totient 13004935725131044942624977631 = 12577541004691749285007808160 := by
  rw [← show
    ((([(31, 1), (1597, 1), (262688826330237036027733, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977631 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_free64ElevenI_1597, prime_free64ElevenI_262688826330237036027733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977632 :
    Nat.totient 13004935725131044942624977632 = 6502467862565522471312488800 := by
  rw [← show
    ((([(2, 5), (406404241410345154457030551, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977632 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_406404241410345154457030551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977633 :
    Nat.totient 13004935725131044942624977633 = 7881779227352148450075744000 := by
  rw [← show
    ((([(3, 1), (11, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977633 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977634 :
    Nat.totient 13004935725131044942624977634 = 6060357291906410768246442240 := by
  rw [← show
    ((([(2, 1), (17, 1), (199, 1), (211, 1), (9109483663880487566509, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977634 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64ElevenI_199, prime_free64ElevenI_211, prime_free64ElevenI_9109483663880487566509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977635 :
    Nat.totient 13004935725131044942624977635 = 8895207556753302679280698752 := by
  rw [← show
    ((([(5, 1), (7, 1), (397, 1), (946695979, 1), (988642159474447, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977635 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_free64ElevenI_397, prime_free64ElevenI_946695979, prime_free64ElevenI_988642159474447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977636 :
    Nat.totient 13004935725131044942624977636 = 4322115135580749261333820416 := by
  rw [← show
    ((([(2, 2), (3, 2), (337, 1), (2779889117, 1), (385610041946069, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977636 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_337, prime_free64ElevenI_2779889117, prime_free64ElevenI_385610041946069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977637 :
    Nat.totient 13004935725131044942624977637 = 12653450975803178863094572800 := by
  rw [← show
    ((([(37, 1), (351484749327866079530404801, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977637 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_free64ElevenI_351484749327866079530404801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977638 :
    Nat.totient 13004935725131044942624977638 = 6105227139784211047797081600 := by
  rw [← show
    ((([(2, 1), (19, 1), (113, 1), (13163, 1), (455471, 1), (470579, 1), (1073490031, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977638 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_113, prime_free64ElevenI_13163, prime_free64ElevenI_455471, prime_free64ElevenI_470579, prime_free64ElevenI_1073490031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977639 :
    Nat.totient 13004935725131044942624977639 = 8002948118165992445902531200 := by
  rw [← show
    ((([(3, 1), (13, 1), (89669, 1), (56990814479, 1), (65252388451, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977639 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_free64ElevenI_89669, prime_free64ElevenI_56990814479, prime_free64ElevenI_65252388451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977640 :
    Nat.totient 13004935725131044942624977640 = 5201974283278365652102560000 := by
  rw [← show
    ((([(2, 3), (5, 1), (767926501, 1), (423378269541287941, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977640 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64ElevenI_767926501, prime_free64ElevenI_423378269541287941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977641 :
    Nat.totient 13004935725131044942624977641 = 12687742140935135493784356000 := by
  rw [← show
    ((([(41, 1), (423992911, 1), (748110513271031791, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977641 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_free64ElevenI_423992911, prime_free64ElevenI_748110513271031791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977642 :
    Nat.totient 13004935725131044942624977642 = 3715695662153179589791976448 := by
  rw [← show
    ((([(2, 1), (3, 1), (7, 1), (14329009, 1), (21609402770898839089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977642 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_free64ElevenI_14329009, prime_free64ElevenI_21609402770898839089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977643 :
    Nat.totient 13004935725131044942624977643 = 12699771255421074380190890304 := by
  rw [← show
    ((([(43, 1), (4663, 1), (36966987433, 1), (1754527902319, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977643 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_free64ElevenI_4663, prime_free64ElevenI_36966987433, prime_free64ElevenI_1754527902319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977644 :
    Nat.totient 13004935725131044942624977644 = 5911334138090495746625955840 := by
  rw [← show
    ((([(2, 2), (11, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977644 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977645 :
    Nat.totient 13004935725131044942624977645 = 6935897228204622879631861728 := by
  rw [← show
    ((([(3, 2), (5, 1), (101267, 1), (2853827719489851348443, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977645 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64ElevenI_101267, prime_free64ElevenI_2853827719489851348443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977646 :
    Nat.totient 13004935725131044942624977646 = 6149867016085418419375170688 := by
  rw [← show
    ((([(2, 1), (23, 1), (89, 1), (3176584202523459927363209, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977646 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_89, prime_free64ElevenI_3176584202523459927363209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977647 :
    Nat.totient 13004935725131044942624977647 = 12679838512242277911209115360 := by
  rw [← show
    ((([(47, 1), (263, 1), (103835981, 1), (10132269515533267, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977647 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_263, prime_free64ElevenI_103835981, prime_free64ElevenI_10132269515533267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977648 :
    Nat.totient 13004935725131044942624977648 = 4334584010475828177170285568 := by
  rw [← show
    ((([(2, 4), (3, 1), (10987, 1), (465392159, 1), (52986933480497, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977648 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_10987, prime_free64ElevenI_465392159, prime_free64ElevenI_52986933480497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977649 :
    Nat.totient 13004935725131044942624977649 = 11097100823750513685827325864 := by
  rw [← show
    ((([(7, 2), (223, 1), (1190165253512496105301087, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977649 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_223, prime_free64ElevenI_1190165253512496105301087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977650 :
    Nat.totient 13004935725131044942624977650 = 5201973648077399585432289360 := by
  rw [← show
    ((([(2, 1), (5, 2), (8103079, 1), (32098750919572782007, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977650 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64ElevenI_8103079, prime_free64ElevenI_32098750919572782007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977651 :
    Nat.totient 13004935725131044942624977651 = 8159959670670459571843122688 := by
  rw [← show
    ((([(3, 1), (17, 2), (14999925865203050683535153, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977651 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_free64ElevenI_14999925865203050683535153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977652 :
    Nat.totient 13004935725131044942624977652 = 5998077658001806198484503680 := by
  rw [← show
    ((([(2, 2), (13, 1), (1429, 1), (174042899, 1), (1005579309916031, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977652 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_free64ElevenI_1429, prime_free64ElevenI_174042899, prime_free64ElevenI_1005579309916031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977653 :
    Nat.totient 13004935725131044942624977653 = 12759559579373855415405638400 := by
  rw [← show
    ((([(53, 1), (245376145757189527219339201, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977653 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_free64ElevenI_245376145757189527219339201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977654 :
    Nat.totient 13004935725131044942624977654 = 4328631607876707003841000296 := by
  rw [← show
    ((([(2, 1), (3, 3), (683, 1), (352609287054146872258147, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977654 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_683, prime_free64ElevenI_352609287054146872258147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977655 :
    Nat.totient 13004935725131044942624977655 = 9458135057715683318239186080 := by
  rw [← show
    ((([(5, 1), (11, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977655 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977656 :
    Nat.totient 13004935725131044942624977656 = 5571885582918388788271257600 := by
  rw [← show
    ((([(2, 3), (7, 1), (3361, 1), (69095803359603035568841, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977656 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_free64ElevenI_3361, prime_free64ElevenI_69095803359603035568841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977657 :
    Nat.totient 13004935725131044942624977657 = 8213353350080862604532341248 := by
  rw [← show
    ((([(3, 1), (19, 1), (28297, 1), (36072713069, 1), (223518848957, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977657 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_free64ElevenI_28297, prime_free64ElevenI_36072713069, prime_free64ElevenI_223518848957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977658 :
    Nat.totient 13004935725131044942624977658 = 6275918695425506631738763312 := by
  rw [← show
    ((([(2, 1), (29, 1), (2699, 1), (83076335584897630940099, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977658 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_free64ElevenI_2699, prime_free64ElevenI_83076335584897630940099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977659 :
    Nat.totient 13004935725131044942624977659 = 12622097459816259035791986816 := by
  rw [← show
    ((([(59, 1), (79, 1), (37547, 1), (50627, 1), (18466379, 1), (79485869, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977659 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_t64_79, prime_free64ElevenI_37547, prime_free64ElevenI_50627, prime_free64ElevenI_18466379, prime_free64ElevenI_79485869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977660 :
    Nat.totient 13004935725131044942624977660 = 3465824385218416679936848128 := by
  rw [← show
    ((([(2, 2), (3, 1), (5, 1), (1607, 1), (8116909, 1), (16616915289683747, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977660 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_free64ElevenI_1607, prime_free64ElevenI_8116909, prime_free64ElevenI_16616915289683747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977661 :
    Nat.totient 13004935725131044942624977661 = 12791740029124838271110058240 := by
  rw [← show
    ((([(61, 1), (450713209, 1), (473018459117534089, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977661 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_free64ElevenI_450713209, prime_free64ElevenI_473018459117534089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977662 :
    Nat.totient 13004935725131044942624977662 = 6292613031497474496631603200 := by
  rw [← show
    ((([(2, 1), (31, 2), (64399, 1), (70846289, 1), (1483059573761, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977662 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_free64ElevenI_64399, prime_free64ElevenI_70846289, prime_free64ElevenI_1483059573761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977663 :
    Nat.totient 13004935725131044942624977663 = 7429567293007416787396845312 := by
  rw [← show
    ((([(3, 2), (7, 1), (4073, 1), (50681942350247058416537, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977663 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_free64ElevenI_4073, prime_free64ElevenI_50681942350247058416537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977664 :
    Nat.totient 13004935725131044942624977664 = 6502411105253563406332428288 := by
  rw [← show
    ((([(2, 8), (146059, 1), (531337, 1), (654590747794993, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977664 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_free64ElevenI_146059, prime_free64ElevenI_531337, prime_free64ElevenI_654590747794993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977665 :
    Nat.totient 13004935725131044942624977665 = 9472084573501495690400710656 := by
  rw [← show
    ((([(5, 1), (13, 1), (73, 1), (2713289, 1), (1010126905894256753, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977665 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_73, prime_free64ElevenI_2713289, prime_free64ElevenI_1010126905894256753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977666 :
    Nat.totient 13004935725131044942624977666 = 3931167071402484278607768960 := by
  rw [← show
    ((([(2, 1), (3, 1), (11, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977666 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977667 :
    Nat.totient 13004935725131044942624977667 = 12978896722316591950704168000 := by
  rw [← show
    ((([(503, 1), (70879, 1), (11347241, 1), (32146401498451, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977667 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_503, prime_free64ElevenI_70879, prime_free64ElevenI_11347241, prime_free64ElevenI_32146401498451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977668 :
    Nat.totient 13004935725131044942624977668 = 6101116410984025639247424000 := by
  rw [← show
    ((([(2, 2), (17, 1), (331, 1), (17099, 1), (850351, 1), (39737666859479, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977668 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_free64ElevenI_331, prime_free64ElevenI_17099, prime_free64ElevenI_850351, prime_free64ElevenI_39737666859479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977669 :
    Nat.totient 13004935725131044942624977669 = 8283701786383015859602369920 := by
  rw [← show
    ((([(3, 1), (23, 1), (1193, 1), (3527, 1), (44793316211528141791, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977669 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_free64ElevenI_1193, prime_free64ElevenI_3527, prime_free64ElevenI_44793316211528141791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977670 :
    Nat.totient 13004935725131044942624977670 = 4417624995030824652809002368 := by
  rw [← show
    ((([(2, 1), (5, 1), (7, 1), (109, 1), (14563, 1), (117039598324332458743, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977670 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_109, prime_free64ElevenI_14563, prime_free64ElevenI_117039598324332458743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977671 :
    Nat.totient 13004935725131044942624977671 = 13004935723373262527576704200 := by
  rw [← show
    ((([(7398490091, 1), (1757782407649783381, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977671 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_7398490091, prime_free64ElevenI_1757782407649783381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977672 :
    Nat.totient 13004935725131044942624977672 = 4334972844296810815070469120 := by
  rw [← show
    ((([(2, 3), (3, 2), (756641, 1), (2986072027, 1), (79943942843, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977672 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_free64ElevenI_756641, prime_free64ElevenI_2986072027, prime_free64ElevenI_79943942843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977673 :
    Nat.totient 13004935725131044942624977673 = 13004847274833317721528989460 := by
  rw [← show
    ((([(147031, 1), (88450297727221095841183, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977673 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_147031, prime_free64ElevenI_88450297727221095841183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977674 :
    Nat.totient 13004935725131044942624977674 = 6281209477160517989499219072 := by
  rw [← show
    ((([(2, 1), (37, 1), (139, 1), (175092814153, 1), (7220933861803, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977674 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_t64_139, prime_free64ElevenI_175092814153, prime_free64ElevenI_7220933861803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977675 :
    Nat.totient 13004935725131044942624977675 = 6872792047029469096413696000 := by
  rw [← show
    ((([(3, 1), (5, 2), (131, 1), (673, 1), (10110253421, 1), (194535356503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977675 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_free64ElevenI_131, prime_t64_673, prime_free64ElevenI_10110253421, prime_free64ElevenI_194535356503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977676 :
    Nat.totient 13004935725131044942624977676 = 6148128618707760230120064000 := by
  rw [← show
    ((([(2, 2), (19, 1), (509, 1), (4168501, 1), (80648617216138289, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977676 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_free64ElevenI_509, prime_free64ElevenI_4168501, prime_free64ElevenI_80648617216138289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977677 :
    Nat.totient 13004935725131044942624977677 = 10111734118010011351069195200 := by
  rw [← show
    ((([(7, 1), (11, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977677 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977678 :
    Nat.totient 13004935725131044942624977678 = 4001518684655706136192300800 := by
  rw [← show
    ((([(2, 1), (3, 1), (13, 1), (166729945193987755674679201, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977678 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_free64ElevenI_166729945193987755674679201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977679 :
    Nat.totient 13004935725131044942624977679 = 13004935725131044942624977678 := by
  rw [← show
    ((([(13004935725131044942624977679, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977679 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_13004935725131044942624977679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977680 :
    Nat.totient 13004935725131044942624977680 = 5201974290052417977049991040 := by
  rw [← show
    ((([(2, 4), (5, 1), (162561696564138061782812221, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977680 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_free64ElevenI_162561696564138061782812221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977681 :
    Nat.totient 13004935725131044942624977681 = 8547845077550921558532847920 := by
  rw [← show
    ((([(3, 3), (71, 1), (6784004029802318697248293, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977681 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_71, prime_free64ElevenI_6784004029802318697248293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977682 :
    Nat.totient 13004935725131044942624977682 = 6343778661718980518232768160 := by
  rw [← show
    ((([(2, 1), (41, 1), (68639, 1), (2310592769937563928959, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977682 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_free64ElevenI_68639, prime_free64ElevenI_2310592769937563928959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977683 :
    Nat.totient 13004935725131044942624977683 = 12679112127118741194383539200 := by
  rw [← show
    ((([(67, 1), (137, 1), (467, 1), (1187, 1), (44101, 1), (57955786438813, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977683 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_67, prime_t64_137, prime_t64_467, prime_free64ElevenI_1187, prime_free64ElevenI_44101, prime_free64ElevenI_57955786438813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977684 :
    Nat.totient 13004935725131044942624977684 = 3670745146822020802527632640 := by
  rw [← show
    ((([(2, 2), (3, 1), (7, 1), (83, 2), (20021, 1), (1122501612778329029, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977684 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_83, prime_free64ElevenI_20021, prime_free64ElevenI_1122501612778329029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977685 :
    Nat.totient 13004935725131044942624977685 = 9688814517331983207923712000 := by
  rw [← show
    ((([(5, 1), (17, 1), (97, 1), (4451, 1), (816353, 1), (434092180506571, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977685 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_t64_97, prime_free64ElevenI_4451, prime_free64ElevenI_816353, prime_free64ElevenI_434092180506571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977686 :
    Nat.totient 13004935725131044942624977686 = 6351225804245330146385087904 := by
  rw [← show
    ((([(2, 1), (43, 1), (378019, 1), (1251703, 1), (319591217957293, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977686 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_free64ElevenI_378019, prime_free64ElevenI_1251703, prime_free64ElevenI_319591217957293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977687 :
    Nat.totient 13004935725131044942624977687 = 8361248066063137401191459424 := by
  rw [← show
    ((([(3, 1), (29, 1), (859, 1), (174018649393588440750739, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977687 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_t64_859, prime_free64ElevenI_174018649393588440750739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977688 :
    Nat.totient 13004935725131044942624977688 = 5880385004793259859191507200 := by
  rw [← show
    ((([(2, 3), (11, 1), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977688 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977689 :
    Nat.totient 13004935725131044942624977689 = 13004935725128344244222617956 := by
  rw [← show
    ((([(4824013975267, 1), (2695874388384467, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977689 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free64ElevenI_4824013975267, prime_free64ElevenI_2695874388384467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977690 :
    Nat.totient 13004935725131044942624977690 = 3467102273313162451405872000 := by
  rw [← show
    ((([(2, 1), (3, 2), (5, 1), (4019, 1), (198851, 1), (13664159, 1), (13232350871, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977690 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_free64ElevenI_4019, prime_free64ElevenI_198851, prime_free64ElevenI_13664159, prime_free64ElevenI_13232350871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977691 :
    Nat.totient 13004935725131044942624977691 = 10289507491656367418821386240 := by
  rw [← show
    ((([(7, 1), (13, 1), (144383, 1), (293179, 1), (1832513, 1), (1842344461, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977691 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_free64ElevenI_144383, prime_free64ElevenI_293179, prime_free64ElevenI_1832513, prime_free64ElevenI_1842344461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977692 :
    Nat.totient 13004935725131044942624977692 = 6219738926222614860814179840 := by
  rw [← show
    ((([(2, 2), (23, 1), (767813, 1), (1284617, 1), (143314870910581, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977692 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_free64ElevenI_767813, prime_free64ElevenI_1284617, prime_free64ElevenI_143314870910581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977693 :
    Nat.totient 13004935725131044942624977693 = 8379320607261279431138603520 := by
  rw [← show
    ((([(3, 1), (31, 1), (773, 1), (78809, 1), (2295461170901659093, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977693 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_free64ElevenI_773, prime_free64ElevenI_78809, prime_free64ElevenI_2295461170901659093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977694 :
    Nat.totient 13004935725131044942624977694 = 6304639728258992066085818400 := by
  rw [← show
    ((([(2, 1), (47, 1), (107, 1), (303537701, 1), (4259748300978343, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977694 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_47, prime_t64_107, prime_free64ElevenI_303537701, prime_free64ElevenI_4259748300978343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free64ElevenI_13004935725131044942624977695 :
    Nat.totient 13004935725131044942624977695 = 9841811553396478723223594880 := by
  rw [← show
    ((([(5, 1), (19, 1), (677, 1), (5207243, 1), (38831850885288871, 1)] : List FactorBlock).map factorBlockValue).prod) = 13004935725131044942624977695 by
      norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_19, prime_free64ElevenI_677, prime_free64ElevenI_5207243, prime_free64ElevenI_38831850885288871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- A free-position kill four below eleven times `periodLcm 64`. -/
theorem freeKill_64ElevenI :
    certifiedKill 1 13004935725131044942624977596 98 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free64ElevenI_13004935725131044942624977597,
    phi_free64ElevenI_13004935725131044942624977598,
    phi_free64ElevenI_13004935725131044942624977599,
    phi_free64ElevenI_13004935725131044942624977600,
    phi_free64ElevenI_13004935725131044942624977601,
    phi_free64ElevenI_13004935725131044942624977602,
    phi_free64ElevenI_13004935725131044942624977603,
    phi_free64ElevenI_13004935725131044942624977604,
    phi_free64ElevenI_13004935725131044942624977605,
    phi_free64ElevenI_13004935725131044942624977606,
    phi_free64ElevenI_13004935725131044942624977607,
    phi_free64ElevenI_13004935725131044942624977608,
    phi_free64ElevenI_13004935725131044942624977609,
    phi_free64ElevenI_13004935725131044942624977610,
    phi_free64ElevenI_13004935725131044942624977611,
    phi_free64ElevenI_13004935725131044942624977612,
    phi_free64ElevenI_13004935725131044942624977613,
    phi_free64ElevenI_13004935725131044942624977614,
    phi_free64ElevenI_13004935725131044942624977615,
    phi_free64ElevenI_13004935725131044942624977616,
    phi_free64ElevenI_13004935725131044942624977617,
    phi_free64ElevenI_13004935725131044942624977618,
    phi_free64ElevenI_13004935725131044942624977619,
    phi_free64ElevenI_13004935725131044942624977620,
    phi_free64ElevenI_13004935725131044942624977621,
    phi_free64ElevenI_13004935725131044942624977622,
    phi_free64ElevenI_13004935725131044942624977623,
    phi_free64ElevenI_13004935725131044942624977624,
    phi_free64ElevenI_13004935725131044942624977625,
    phi_free64ElevenI_13004935725131044942624977626,
    phi_free64ElevenI_13004935725131044942624977627,
    phi_free64ElevenI_13004935725131044942624977628,
    phi_free64ElevenI_13004935725131044942624977629,
    phi_free64ElevenI_13004935725131044942624977630,
    phi_free64ElevenI_13004935725131044942624977631,
    phi_free64ElevenI_13004935725131044942624977632,
    phi_free64ElevenI_13004935725131044942624977633,
    phi_free64ElevenI_13004935725131044942624977634,
    phi_free64ElevenI_13004935725131044942624977635,
    phi_free64ElevenI_13004935725131044942624977636,
    phi_free64ElevenI_13004935725131044942624977637,
    phi_free64ElevenI_13004935725131044942624977638,
    phi_free64ElevenI_13004935725131044942624977639,
    phi_free64ElevenI_13004935725131044942624977640,
    phi_free64ElevenI_13004935725131044942624977641,
    phi_free64ElevenI_13004935725131044942624977642,
    phi_free64ElevenI_13004935725131044942624977643,
    phi_free64ElevenI_13004935725131044942624977644,
    phi_free64ElevenI_13004935725131044942624977645,
    phi_free64ElevenI_13004935725131044942624977646,
    phi_free64ElevenI_13004935725131044942624977647,
    phi_free64ElevenI_13004935725131044942624977648,
    phi_free64ElevenI_13004935725131044942624977649,
    phi_free64ElevenI_13004935725131044942624977650,
    phi_free64ElevenI_13004935725131044942624977651,
    phi_free64ElevenI_13004935725131044942624977652,
    phi_free64ElevenI_13004935725131044942624977653,
    phi_free64ElevenI_13004935725131044942624977654,
    phi_free64ElevenI_13004935725131044942624977655,
    phi_free64ElevenI_13004935725131044942624977656,
    phi_free64ElevenI_13004935725131044942624977657,
    phi_free64ElevenI_13004935725131044942624977658,
    phi_free64ElevenI_13004935725131044942624977659,
    phi_free64ElevenI_13004935725131044942624977660,
    phi_free64ElevenI_13004935725131044942624977661,
    phi_free64ElevenI_13004935725131044942624977662,
    phi_free64ElevenI_13004935725131044942624977663,
    phi_free64ElevenI_13004935725131044942624977664,
    phi_free64ElevenI_13004935725131044942624977665,
    phi_free64ElevenI_13004935725131044942624977666,
    phi_free64ElevenI_13004935725131044942624977667,
    phi_free64ElevenI_13004935725131044942624977668,
    phi_free64ElevenI_13004935725131044942624977669,
    phi_free64ElevenI_13004935725131044942624977670,
    phi_free64ElevenI_13004935725131044942624977671,
    phi_free64ElevenI_13004935725131044942624977672,
    phi_free64ElevenI_13004935725131044942624977673,
    phi_free64ElevenI_13004935725131044942624977674,
    phi_free64ElevenI_13004935725131044942624977675,
    phi_free64ElevenI_13004935725131044942624977676,
    phi_free64ElevenI_13004935725131044942624977677,
    phi_free64ElevenI_13004935725131044942624977678,
    phi_free64ElevenI_13004935725131044942624977679,
    phi_free64ElevenI_13004935725131044942624977680,
    phi_free64ElevenI_13004935725131044942624977681,
    phi_free64ElevenI_13004935725131044942624977682,
    phi_free64ElevenI_13004935725131044942624977683,
    phi_free64ElevenI_13004935725131044942624977684,
    phi_free64ElevenI_13004935725131044942624977685,
    phi_free64ElevenI_13004935725131044942624977686,
    phi_free64ElevenI_13004935725131044942624977687,
    phi_free64ElevenI_13004935725131044942624977688,
    phi_free64ElevenI_13004935725131044942624977689,
    phi_free64ElevenI_13004935725131044942624977690,
    phi_free64ElevenI_13004935725131044942624977691,
    phi_free64ElevenI_13004935725131044942624977692,
    phi_free64ElevenI_13004935725131044942624977693,
    phi_free64ElevenI_13004935725131044942624977694,
    phi_free64ElevenI_13004935725131044942624977695]

end TotientTailPeriodKiller
end Erdos249257
