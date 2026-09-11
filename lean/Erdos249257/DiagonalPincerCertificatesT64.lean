import Erdos249257.DiagonalPincerCertificatesT61
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=64 diagonal-pincer certificate

This generated extension consumes 175 new large-prime Lucas roots
and 1067 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 186 Euler totients in the t=64 window, and proves the
twenty-eighth finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=64 window -/

private theorem prime_t64_2 : Nat.Prime 2 := by norm_num
private theorem prime_t64_3 : Nat.Prime 3 := by norm_num
private theorem prime_t64_5 : Nat.Prime 5 := by norm_num
private theorem prime_t64_7 : Nat.Prime 7 := by norm_num
private theorem prime_t64_11 : Nat.Prime 11 := by norm_num
private theorem prime_t64_13 : Nat.Prime 13 := by norm_num
private theorem prime_t64_17 : Nat.Prime 17 := by norm_num
private theorem prime_t64_19 : Nat.Prime 19 := by norm_num
private theorem prime_t64_23 : Nat.Prime 23 := by norm_num
private theorem prime_t64_29 : Nat.Prime 29 := by norm_num
private theorem prime_t64_31 : Nat.Prime 31 := by norm_num
private theorem prime_t64_37 : Nat.Prime 37 := by norm_num
private theorem prime_t64_41 : Nat.Prime 41 := by norm_num
private theorem prime_t64_43 : Nat.Prime 43 := by norm_num
private theorem prime_t64_47 : Nat.Prime 47 := by norm_num
private theorem prime_t64_53 : Nat.Prime 53 := by norm_num
private theorem prime_t64_59 : Nat.Prime 59 := by norm_num
private theorem prime_t64_61 : Nat.Prime 61 := by norm_num
private theorem prime_t64_67 : Nat.Prime 67 := by norm_num
private theorem prime_t64_71 : Nat.Prime 71 := by norm_num
private theorem prime_t64_73 : Nat.Prime 73 := by norm_num
private theorem prime_t64_79 : Nat.Prime 79 := by norm_num
private theorem prime_t64_83 : Nat.Prime 83 := by norm_num
private theorem prime_t64_89 : Nat.Prime 89 := by norm_num
private theorem prime_t64_97 : Nat.Prime 97 := by norm_num
private theorem prime_t64_101 : Nat.Prime 101 := by norm_num
private theorem prime_t64_103 : Nat.Prime 103 := by norm_num
private theorem prime_t64_107 : Nat.Prime 107 := by norm_num
private theorem prime_t64_109 : Nat.Prime 109 := by norm_num
private theorem prime_t64_113 : Nat.Prime 113 := by norm_num
private theorem prime_t64_137 : Nat.Prime 137 := by norm_num
private theorem prime_t64_139 : Nat.Prime 139 := by norm_num
private theorem prime_t64_149 : Nat.Prime 149 := by norm_num
private theorem prime_t64_157 : Nat.Prime 157 := by norm_num
private theorem prime_t64_163 : Nat.Prime 163 := by norm_num
private theorem prime_t64_167 : Nat.Prime 167 := by norm_num
private theorem prime_t64_179 : Nat.Prime 179 := by norm_num
private theorem prime_t64_191 : Nat.Prime 191 := by norm_num
private theorem prime_t64_193 : Nat.Prime 193 := by norm_num
private theorem prime_t64_197 : Nat.Prime 197 := by norm_num
private theorem prime_t64_223 : Nat.Prime 223 := by norm_num
private theorem prime_t64_227 : Nat.Prime 227 := by norm_num
private theorem prime_t64_229 : Nat.Prime 229 := by norm_num
private theorem prime_t64_233 : Nat.Prime 233 := by norm_num
private theorem prime_t64_239 : Nat.Prime 239 := by norm_num
private theorem prime_t64_251 : Nat.Prime 251 := by norm_num
private theorem prime_t64_263 : Nat.Prime 263 := by norm_num
private theorem prime_t64_269 : Nat.Prime 269 := by norm_num
private theorem prime_t64_283 : Nat.Prime 283 := by norm_num
private theorem prime_t64_307 : Nat.Prime 307 := by norm_num
private theorem prime_t64_311 : Nat.Prime 311 := by norm_num
private theorem prime_t64_317 : Nat.Prime 317 := by norm_num
private theorem prime_t64_349 : Nat.Prime 349 := by norm_num
private theorem prime_t64_383 : Nat.Prime 383 := by norm_num
private theorem prime_t64_409 : Nat.Prime 409 := by norm_num
private theorem prime_t64_421 : Nat.Prime 421 := by norm_num
private theorem prime_t64_431 : Nat.Prime 431 := by norm_num
private theorem prime_t64_433 : Nat.Prime 433 := by norm_num
private theorem prime_t64_439 : Nat.Prime 439 := by norm_num
private theorem prime_t64_461 : Nat.Prime 461 := by norm_num
private theorem prime_t64_467 : Nat.Prime 467 := by norm_num
private theorem prime_t64_479 : Nat.Prime 479 := by norm_num
private theorem prime_t64_491 : Nat.Prime 491 := by norm_num
private theorem prime_t64_499 : Nat.Prime 499 := by norm_num
private theorem prime_t64_521 : Nat.Prime 521 := by norm_num
private theorem prime_t64_563 : Nat.Prime 563 := by norm_num
private theorem prime_t64_607 : Nat.Prime 607 := by norm_num
private theorem prime_t64_617 : Nat.Prime 617 := by norm_num
private theorem prime_t64_641 : Nat.Prime 641 := by norm_num
private theorem prime_t64_647 : Nat.Prime 647 := by norm_num
private theorem prime_t64_661 : Nat.Prime 661 := by norm_num
private theorem prime_t64_673 : Nat.Prime 673 := by norm_num
private theorem prime_t64_683 : Nat.Prime 683 := by norm_num
private theorem prime_t64_719 : Nat.Prime 719 := by norm_num
private theorem prime_t64_751 : Nat.Prime 751 := by norm_num
private theorem prime_t64_761 : Nat.Prime 761 := by norm_num
private theorem prime_t64_787 : Nat.Prime 787 := by norm_num
private theorem prime_t64_859 : Nat.Prime 859 := by norm_num
private theorem prime_t64_883 : Nat.Prime 883 := by norm_num
private theorem prime_t64_991 : Nat.Prime 991 := by norm_num
private theorem prime_t64_997 : Nat.Prime 997 := by norm_num
private theorem prime_t64_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_t64_1061 : Nat.Prime 1061 := by norm_num
private theorem prime_t64_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_t64_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_t64_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_t64_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_t64_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_t64_1213 : Nat.Prime 1213 := by norm_num
private theorem prime_t64_1229 : Nat.Prime 1229 := by norm_num
private theorem prime_t64_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_t64_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_t64_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_t64_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_t64_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_t64_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_t64_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_t64_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_t64_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_t64_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_t64_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_t64_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_t64_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_t64_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_t64_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_t64_2417 : Nat.Prime 2417 := by norm_num
private theorem prime_t64_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_t64_2909 : Nat.Prime 2909 := by norm_num
private theorem prime_t64_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_t64_2963 : Nat.Prime 2963 := by norm_num
private theorem prime_t64_3121 : Nat.Prime 3121 := by norm_num
private theorem prime_t64_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_t64_3511 : Nat.Prime 3511 := by norm_num
private theorem prime_t64_3697 : Nat.Prime 3697 := by norm_num
private theorem prime_t64_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_t64_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_t64_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_t64_4133 : Nat.Prime 4133 := by norm_num
private theorem prime_t64_4271 : Nat.Prime 4271 := by norm_num
private theorem prime_t64_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_t64_4787 : Nat.Prime 4787 := by norm_num
private theorem prime_t64_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_t64_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_t64_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_t64_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_t64_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_t64_6653 : Nat.Prime 6653 := by norm_num
private theorem prime_t64_7669 : Nat.Prime 7669 := by norm_num
private theorem prime_t64_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_t64_7901 : Nat.Prime 7901 := by norm_num
private theorem prime_t64_8093 : Nat.Prime 8093 := by norm_num
private theorem prime_t64_8543 : Nat.Prime 8543 := by norm_num
private theorem prime_t64_9343 : Nat.Prime 9343 := by norm_num
private theorem prime_t64_9829 : Nat.Prime 9829 := by norm_num
private theorem prime_t64_10337 : Nat.Prime 10337 := by norm_num
private theorem prime_t64_10709 : Nat.Prime 10709 := by norm_num
private theorem prime_t64_10789 : Nat.Prime 10789 := by norm_num
private theorem prime_t64_11113 : Nat.Prime 11113 := by norm_num
private theorem prime_t64_12497 : Nat.Prime 12497 := by norm_num
private theorem prime_t64_13709 : Nat.Prime 13709 := by norm_num
private theorem prime_t64_16603 : Nat.Prime 16603 := by norm_num
private theorem prime_t64_16993 : Nat.Prime 16993 := by norm_num
private theorem prime_t64_19759 : Nat.Prime 19759 := by norm_num
private theorem prime_t64_28621 : Nat.Prime 28621 := by norm_num
private theorem prime_t64_31337 : Nat.Prime 31337 := by norm_num
private theorem prime_t64_31397 : Nat.Prime 31397 := by norm_num
private theorem prime_t64_36073 : Nat.Prime 36073 := by norm_num
private theorem prime_t64_38329 : Nat.Prime 38329 := by norm_num
private theorem prime_t64_39551 : Nat.Prime 39551 := by norm_num
private theorem prime_t64_41221 : Nat.Prime 41221 := by norm_num
private theorem prime_t64_44741 : Nat.Prime 44741 := by norm_num
private theorem prime_t64_44959 : Nat.Prime 44959 := by norm_num
private theorem prime_t64_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_t64_48337 : Nat.Prime 48337 := by norm_num
private theorem prime_t64_52453 : Nat.Prime 52453 := by norm_num
private theorem prime_t64_58231 : Nat.Prime 58231 := by norm_num
private theorem prime_t64_65353 : Nat.Prime 65353 := by norm_num
private theorem prime_t64_76697 : Nat.Prime 76697 := by norm_num
private theorem prime_t64_90931 : Nat.Prime 90931 := by norm_num
private theorem prime_t64_94111 : Nat.Prime 94111 := by norm_num
private theorem prime_t64_97523 : Nat.Prime 97523 := by norm_num
private theorem prime_t64_106721 : Nat.Prime 106721 := by norm_num
private theorem prime_t64_116689 : Nat.Prime 116689 := by norm_num
private theorem prime_t64_117833 : Nat.Prime 117833 := by norm_num
private theorem prime_t64_120293 : Nat.Prime 120293 := by norm_num
private theorem prime_t64_125029 : Nat.Prime 125029 := by norm_num
private theorem prime_t64_138977 : Nat.Prime 138977 := by norm_num
private theorem prime_t64_149059 : Nat.Prime 149059 := by norm_num
private theorem prime_t64_152377 : Nat.Prime 152377 := by norm_num
private theorem prime_t64_174749 : Nat.Prime 174749 := by norm_num
private theorem prime_t64_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_t64_235679 : Nat.Prime 235679 := by norm_num
private theorem prime_t64_241513 : Nat.Prime 241513 := by norm_num
private theorem prime_t64_272659 : Nat.Prime 272659 := by norm_num
private theorem prime_t64_309667 : Nat.Prime 309667 := by norm_num
private theorem prime_t64_350737 : Nat.Prime 350737 := by norm_num
private theorem prime_t64_409993 : Nat.Prime 409993 := by norm_num
private theorem prime_t64_509833 : Nat.Prime 509833 := by norm_num
private theorem prime_t64_582643 : Nat.Prime 582643 := by norm_num
private theorem prime_t64_622577 : Nat.Prime 622577 := by norm_num
private theorem prime_t64_623279 : Nat.Prime 623279 := by norm_num
private theorem prime_t64_654163 : Nat.Prime 654163 := by norm_num
private theorem prime_t64_714151 : Nat.Prime 714151 := by norm_num
private theorem prime_t64_911749 : Nat.Prime 911749 := by norm_num
private theorem prime_t64_940369 : Nat.Prime 940369 := by norm_num
private theorem prime_t64_945103 : Nat.Prime 945103 := by norm_num
private theorem prime_t64_1115447 : Nat.Prime 1115447 := by norm_num
private theorem prime_t64_1214459 : Nat.Prime 1214459 := by norm_num
private theorem prime_t64_1216561 : Nat.Prime 1216561 := by norm_num
private theorem prime_t64_1276501 : Nat.Prime 1276501 := by norm_num
private theorem prime_t64_1319293 : Nat.Prime 1319293 := by norm_num
private theorem prime_t64_1632209 : Nat.Prime 1632209 := by norm_num
private theorem prime_t64_1674649 : Nat.Prime 1674649 := by norm_num
private theorem prime_t64_1789993 : Nat.Prime 1789993 := by norm_num
private theorem prime_t64_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_t64_2106407 : Nat.Prime 2106407 := by norm_num
private theorem prime_t64_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_t64_2970893 : Nat.Prime 2970893 := by norm_num
private theorem prime_t64_3623449 : Nat.Prime 3623449 := by norm_num
private theorem prime_t64_3748763 : Nat.Prime 3748763 := by norm_num
private theorem prime_t64_4107799 : Nat.Prime 4107799 := by norm_num
private theorem prime_t64_4597727 : Nat.Prime 4597727 := by norm_num
private theorem prime_t64_5160187 : Nat.Prime 5160187 := by norm_num
private theorem prime_t64_5234927 : Nat.Prime 5234927 := by norm_num
private theorem prime_t64_5250043 : Nat.Prime 5250043 := by norm_num
private theorem prime_t64_6141409 : Nat.Prime 6141409 := by norm_num
private theorem prime_t64_6947861 : Nat.Prime 6947861 := by norm_num
private theorem prime_t64_7478579 : Nat.Prime 7478579 := by norm_num
private theorem prime_t64_7679389 : Nat.Prime 7679389 := by norm_num
private theorem prime_t64_8109733 : Nat.Prime 8109733 := by norm_num
private theorem prime_t64_8295863 : Nat.Prime 8295863 := by norm_num
private theorem prime_t64_8724377 : Nat.Prime 8724377 := by norm_num
private theorem prime_t64_8943971 : Nat.Prime 8943971 := by norm_num
private theorem prime_t64_9238457 : Nat.Prime 9238457 := by norm_num
private theorem prime_t64_9492089 : Nat.Prime 9492089 := by norm_num
private theorem prime_t64_9743417 : Nat.Prime 9743417 := by norm_num
private theorem prime_t64_11383279 : Nat.Prime 11383279 := by norm_num
private theorem prime_t64_11633099 : Nat.Prime 11633099 := by norm_num
private theorem prime_t64_12040159 : Nat.Prime 12040159 := by norm_num
private theorem prime_t64_16364731 : Nat.Prime 16364731 := by norm_num
private theorem prime_t64_16951937 : Nat.Prime 16951937 := by norm_num
private theorem prime_t64_18173501 : Nat.Prime 18173501 := by norm_num
private theorem prime_t64_18689423 : Nat.Prime 18689423 := by norm_num
private theorem prime_t64_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_t64_25210021 : Nat.Prime 25210021 := by norm_num
private theorem prime_t64_26854931 : Nat.Prime 26854931 := by norm_num

/-! ## Exact t=64 window totients -/

private theorem phi_t64_1182266884102822267511361601 : Nat.totient 1182266884102822267511361601 = 1170554827853295639500976192 := by
  rw [← show ((([(103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361602 : Nat.totient 1182266884102822267511361602 = 591133441567912245382206100 := by
  rw [← show ((([(2, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361603 : Nat.totient 1182266884102822267511361603 = 788177922735214845007574400 := by
  rw [← show ((([(3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361604 : Nat.totient 1182266884102822267511361604 = 591133413809049574662595584 := by
  rw [← show ((([(2, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361605 : Nat.totient 1182266884102822267511361605 = 945813505771568331823918608 := by
  rw [← show ((([(5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361606 : Nat.totient 1182266884102822267511361606 = 393116707140248427860776896 := by
  rw [← show ((([(2, 1), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361607 : Nat.totient 1182266884102822267511361607 = 1011173411801001135106919520 := by
  rw [← show ((([(7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361608 : Nat.totient 1182266884102822267511361608 = 588038500479325985919150720 := by
  rw [← show ((([(2, 3), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361609 : Nat.totient 1182266884102822267511361609 = 788177922735214845007574400 := by
  rw [← show ((([(3, 2), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361610 : Nat.totient 1182266884102822267511361610 = 468224508555573175252024000 := by
  rw [← show ((([(2, 1), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361611 : Nat.totient 1182266884102822267511361611 = 1074788076457111152283056000 := by
  rw [← show ((([(11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361612 : Nat.totient 1182266884102822267511361612 = 392821442123895009583726080 := by
  rw [← show ((([(2, 2), (3, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_311, prime_t64_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361613 : Nat.totient 1182266884102822267511361613 = 1091322450430260586490332224 := by
  rw [← show ((([(13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_t64_1319293, prime_lucas_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361614 : Nat.totient 1182266884102822267511361614 = 504829729102411431936000000 := by
  rw [← show ((([(2, 1), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_433, prime_t64_751, prime_t64_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361615 : Nat.totient 1182266884102822267511361615 = 630542218085853059114011296 := by
  rw [← show ((([(3, 1), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_5250043, prime_lucas_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361616 : Nat.totient 1182266884102822267511361616 = 591133442048449901100654336 := by
  rw [← show ((([(2, 4), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361617 : Nat.totient 1182266884102822267511361617 = 1112721773273244487069516800 := by
  rw [← show ((([(17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_lucas_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361618 : Nat.totient 1182266884102822267511361618 = 393372004097683553918976000 := by
  rw [← show ((([(2, 1), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_1051, prime_t64_1153, prime_t64_940369, prime_t64_6947861, prime_t64_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361619 : Nat.totient 1182266884102822267511361619 = 1118619131698437065522004456 := by
  rw [← show ((([(19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_t64_787, prime_lucas_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361620 : Nat.totient 1182266884102822267511361620 = 469454879526960082865824256 := by
  rw [← show ((([(2, 2), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_137, prime_lucas_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361621 : Nat.totient 1182266884102822267511361621 = 674536901859503806414070064 := by
  rw [← show ((([(3, 1), (7, 1), (647, 1), (87014564223362204129783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_647, prime_lucas_87014564223362204129783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361622 : Nat.totient 1182266884102822267511361622 = 537385815227551847710137600 := by
  rw [← show ((([(2, 1), (11, 1), (65353, 1), (10672982981, 1), (77044474757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_65353, prime_lucas_10672982981, prime_lucas_77044474757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361623 : Nat.totient 1182266884102822267511361623 = 1130720846877228034389940000 := by
  rw [← show ((([(23, 1), (7901, 1), (6505873687440897781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_7901, prime_lucas_6505873687440897781301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361624 : Nat.totient 1182266884102822267511361624 = 390509994103978827648837120 := by
  rw [← show ((([(2, 3), (3, 1), (113, 1), (4271, 1), (102069566040058032487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_113, prime_t64_4271, prime_lucas_102069566040058032487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361625 : Nat.totient 1182266884102822267511361625 = 945807159723492911330304000 := by
  rw [← show ((([(5, 3), (149059, 1), (407047681, 1), (155884173167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_149059, prime_lucas_407047681, prime_lucas_155884173167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361626 : Nat.totient 1182266884102822267511361626 = 545661533072139799134615120 := by
  rw [← show ((([(2, 1), (13, 2), (5160187, 1), (677849662823399071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_5160187, prime_lucas_677849662823399071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361627 : Nat.totient 1182266884102822267511361627 = 788177922734890937629881576 := by
  rw [← show ((([(3, 3), (2901032068267, 1), (15093822248003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_2901032068267, prime_lucas_15093822248003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361628 : Nat.totient 1182266884102822267511361628 = 501950187797409469280195136 := by
  rw [← show ((([(2, 2), (7, 1), (107, 1), (2106407, 1), (187340392836749749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_107, prime_t64_2106407, prime_lucas_187340392836749749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361629 : Nat.totient 1182266884102822267511361629 = 1141213757073801325196800000 := by
  rw [← show ((([(29, 1), (4001, 1), (10189408545301797546401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_t64_4001, prime_lucas_10189408545301797546401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361630 : Nat.totient 1182266884102822267511361630 = 315271142909118688380689952 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (12040159, 1), (3273120906190752319, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_12040159, prime_lucas_3273120906190752319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361631 : Nat.totient 1182266884102822267511361631 = 1143324662113825832429601120 := by
  rw [← show ((([(31, 1), (1423, 1), (3748763, 1), (4597727, 1), (1554954787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_t64_1423, prime_t64_3748763, prime_t64_4597727, prime_lucas_1554954787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361632 : Nat.totient 1182266884102822267511361632 = 586370795341124715180480000 := by
  rw [← show ((([(2, 5), (139, 1), (1151, 1), (1214653051, 1), (190117973909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_139, prime_t64_1151, prime_lucas_1214653051, prime_lucas_190117973909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361633 : Nat.totient 1182266884102822267511361633 = 716525294224298420086473600 := by
  rw [← show ((([(3, 1), (11, 2), (11633099, 1), (25210021, 1), (11105555029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_t64_11633099, prime_t64_25210021, prime_lucas_11105555029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361634 : Nat.totient 1182266884102822267511361634 = 555245934677454242900955648 := by
  rw [← show ((([(2, 1), (17, 1), (499, 1), (1965292547, 1), (35457560705417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_499, prime_lucas_1965292547, prime_lucas_35457560705417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361635 : Nat.totient 1182266884102822267511361635 = 807189700743848057422556160 := by
  rw [← show ((([(5, 1), (7, 1), (233, 1), (28621, 1), (5065318471177066877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_t64_233, prime_t64_28621, prime_lucas_5065318471177066877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361636 : Nat.totient 1182266884102822267511361636 = 394088961367607422503787200 := by
  rw [← show ((([(2, 2), (3, 2), (32840746780633951875315601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_32840746780633951875315601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361637 : Nat.totient 1182266884102822267511361637 = 1146690578612362057176672000 := by
  rw [← show ((([(37, 1), (431, 1), (1973, 1), (3187, 1), (90931, 1), (129662805691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_t64_431, prime_t64_1973, prime_t64_3187, prime_t64_90931, prime_lucas_129662805691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361638 : Nat.totient 1182266884102822267511361638 = 551662630915019828234849280 := by
  rw [← show ((([(2, 1), (19, 1), (67, 1), (442529322881, 1), (1049337207563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_67, prime_lucas_442529322881, prime_lucas_1049337207563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361639 : Nat.totient 1182266884102822267511361639 = 727531201799207407228982400 := by
  rw [← show ((([(3, 1), (13, 1), (41221, 1), (735414848980275965581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_t64_41221, prime_lucas_735414848980275965581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361640 : Nat.totient 1182266884102822267511361640 = 471362371250403716287432704 := by
  rw [← show ((([(2, 3), (5, 1), (307, 1), (120293, 1), (9238457, 1), (86631804463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_307, prime_t64_120293, prime_t64_9238457, prime_lucas_86631804463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361641 : Nat.totient 1182266884102822267511361641 = 1146211887247010197130649600 := by
  rw [← show ((([(41, 1), (167, 1), (3769, 1), (138977, 1), (329644722325231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_167, prime_t64_3769, prime_t64_138977, prime_lucas_329644722325231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361642 : Nat.totient 1182266884102822267511361642 = 337790531929316882839574976 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (64596797, 1), (398497559, 1), (1093527187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_lucas_64596797, prime_lucas_398497559, prime_lucas_1093527187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361643 : Nat.totient 1182266884102822267511361643 = 1142867436261497695543447296 := by
  rw [← show ((([(43, 1), (97, 1), (87628772527, 1), (3234659767279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_t64_97, prime_lucas_87628772527, prime_lucas_3234659767279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361644 : Nat.totient 1182266884102822267511361644 = 537393285734981768129250000 := by
  rw [← show ((([(2, 2), (11, 1), (714151, 1), (37624678690399899751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_714151, prime_lucas_37624678690399899751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361645 : Nat.totient 1182266884102822267511361645 = 627605493218555954201814528 := by
  rw [← show ((([(3, 2), (5, 1), (223, 1), (5743, 1), (20514424207990512529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_223, prime_t64_5743, prime_lucas_20514424207990512529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361646 : Nat.totient 1182266884102822267511361646 = 560244538617532051776422688 := by
  rw [← show ((([(2, 1), (23, 1), (109, 1), (235793155983809786101189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_109, prime_lucas_235793155983809786101189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361647 : Nat.totient 1182266884102822267511361647 = 1157112269547443070330268800 := by
  rw [← show ((([(47, 1), (25154614555379197181092801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_lucas_25154614555379197181092801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361648 : Nat.totient 1182266884102822267511361648 = 394088961356920906224190912 := by
  rw [← show ((([(2, 4), (3, 1), (36879251603, 1), (667870388223167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_36879251603, prime_lucas_667870388223167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361649 : Nat.totient 1182266884102822267511361649 = 1013239991148036941565645768 := by
  rw [← show ((([(7, 2), (7699, 1), (3133899934268755463899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_7699, prime_lucas_3133899934268755463899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361650 : Nat.totient 1182266884102822267511361650 = 471745600609307262381587520 := by
  rw [← show ((([(2, 1), (5, 2), (467, 1), (5059, 1), (8543, 1), (1171530377614327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_467, prime_t64_5059, prime_t64_8543, prime_lucas_1171530377614327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361651 : Nat.totient 1182266884102822267511361651 = 740215110912404325369924096 := by
  rw [← show ((([(3, 1), (17, 1), (1103, 1), (1579, 1), (1619, 1), (8221306843187167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_1103, prime_t64_1579, prime_t64_1619, prime_lucas_8221306843187167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361652 : Nat.totient 1182266884102822267511361652 = 543521773192164497804212992 := by
  rw [← show ((([(2, 2), (13, 1), (439, 1), (607, 1), (85321595874110948137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_439, prime_t64_607, prime_lucas_85321595874110948137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361653 : Nat.totient 1182266884102822267511361653 = 1156931345673110080390427344 := by
  rw [← show ((([(53, 1), (383, 1), (58242617079798131312447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_t64_383, prime_lucas_58242617079798131312447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361654 : Nat.totient 1182266884102822267511361654 = 394064646578304014776854528 := by
  rw [← show ((([(2, 1), (3, 4), (16993, 1), (350737, 1), (1224472032347387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_16993, prime_t64_350737, prime_lucas_1224472032347387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361655 : Nat.totient 1182266884102822267511361655 = 859830461145444416251161760 := by
  rw [← show ((([(5, 1), (11, 1), (42475852319, 1), (506070163529759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_lucas_42475852319, prime_lucas_506070163529759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361656 : Nat.totient 1182266884102822267511361656 = 506393995115927594727014400 := by
  rw [← show ((([(2, 3), (7, 1), (1801, 1), (48337, 1), (242512479730968673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_1801, prime_t64_48337, prime_lucas_242512479730968673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361657 : Nat.totient 1182266884102822267511361657 = 746694874096460483706129600 := by
  rw [← show ((([(3, 1), (19, 1), (10125680021, 1), (2048408031805181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_lucas_10125680021, prime_lucas_2048408031805181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361658 : Nat.totient 1182266884102822267511361658 = 570749180577339235363290112 := by
  rw [← show ((([(2, 1), (29, 1), (1632209, 1), (12488542701869825489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_t64_1632209, prime_lucas_12488542701869825489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361659 : Nat.totient 1182266884102822267511361659 = 1116690320675732589273876480 := by
  rw [← show ((([(59, 1), (71, 1), (73, 1), (157, 1), (179, 1), (137571863802922249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_t64_71, prime_t64_73, prime_t64_157, prime_t64_179, prime_lucas_137571863802922249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361660 : Nat.totient 1182266884102822267511361660 = 314779249766910364629442560 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (641, 1), (4107799, 1), (7483367271236279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_641, prime_t64_4107799, prime_lucas_7483367271236279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361661 : Nat.totient 1182266884102822267511361661 = 1162885459773267804109536000 := by
  rw [← show ((([(61, 1), (19381424329554463401825601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_lucas_19381424329554463401825601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361662 : Nat.totient 1182266884102822267511361662 = 571909862521123611303772800 := by
  rw [← show ((([(2, 1), (31, 1), (3697, 1), (26854931, 1), (192065934654443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_t64_3697, prime_t64_26854931, prime_lucas_192065934654443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361663 : Nat.totient 1182266884102822267511361663 = 675569474887527660887283600 := by
  rw [← show ((([(3, 2), (7, 1), (58231, 1), (322270629346999284871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_58231, prime_lucas_322270629346999284871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361664 : Nat.totient 1182266884102822267511361664 = 591013609608262662007188480 := by
  rw [← show ((([(2, 7), (4933, 1), (1872381924194871065261, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_4933, prime_lucas_1872381924194871065261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361665 : Nat.totient 1182266884102822267511361665 = 872570607225700806526079232 := by
  rw [← show ((([(5, 1), (13, 1), (1789, 1), (10166976687473210366869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_1789, prime_lucas_10166976687473210366869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361666 : Nat.totient 1182266884102822267511361666 = 355856313494523600720000000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (251, 1), (563, 1), (2027, 1), (2251, 1), (31397, 1), (884854933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_251, prime_t64_563, prime_t64_2027, prime_t64_2251, prime_t64_31397, prime_lucas_884854933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361667 : Nat.totient 1182266884102822267511361667 = 1180488778993030262497327872 := by
  rw [← show ((([(683, 1), (31337, 1), (125029, 1), (441800950636813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_683, prime_t64_31337, prime_t64_125029, prime_lucas_441800950636813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361668 : Nat.totient 1182266884102822267511361668 = 547951484092145593050759168 := by
  rw [← show ((([(2, 2), (17, 1), (83, 1), (617, 1), (673, 1), (504461807457102067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_83, prime_t64_617, prime_t64_673, prime_lucas_504461807457102067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361669 : Nat.totient 1182266884102822267511361669 = 753901306546637351634087600 := by
  rw [← show ((([(3, 1), (23, 1), (94111, 1), (182064824177373999391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_t64_94111, prime_lucas_182064824177373999391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361670 : Nat.totient 1182266884102822267511361670 = 400193965897803183515295744 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (79, 1), (19759, 1), (116689, 1), (92724716540689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_79, prime_t64_19759, prime_t64_116689, prime_lucas_92724716540689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361671 : Nat.totient 1182266884102822267511361671 = 1175430706123956741727285248 := by
  rw [← show ((([(197, 1), (1409, 1), (4036298429, 1), (1055249212663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_197, prime_t64_1409, prime_lucas_4036298429, prime_lucas_1055249212663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361672 : Nat.totient 1182266884102822267511361672 = 393916119844877028706664448 := by
  rw [← show ((([(2, 3), (3, 2), (2957, 1), (10709, 1), (272659, 1), (309667, 1), (6141409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_2957, prime_t64_10709, prime_t64_272659, prime_t64_309667, prime_t64_6141409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361673 : Nat.totient 1182266884102822267511361673 = 1181901862876059772829464320 := by
  rw [← show ((([(3739, 1), (44959, 1), (52453, 1), (134082804329041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3739, prime_t64_44959, prime_t64_52453, prime_lucas_134082804329041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361674 : Nat.totient 1182266884102822267511361674 = 574901357052520003815590400 := by
  rw [← show ((([(2, 1), (37, 1), (2281, 1), (174749, 1), (8943971, 1), (4481397199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_t64_2281, prime_t64_174749, prime_t64_8943971, prime_lucas_4481397199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361675 : Nat.totient 1182266884102822267511361675 = 630541255977730511078556960 := by
  rw [← show ((([(3, 1), (5, 2), (582643, 1), (27055261034122604923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_582643, prime_lucas_27055261034122604923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361676 : Nat.totient 1182266884102822267511361676 = 557891796972324622814622720 := by
  rw [← show ((([(2, 2), (19, 1), (263, 1), (859443911, 1), (68822214862657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_263, prime_lucas_859443911, prime_lucas_68822214862657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361677 : Nat.totient 1182266884102822267511361677 = 907883012113761636281472000 := by
  rw [← show ((([(7, 1), (11, 1), (89, 1), (521, 1), (719, 1), (460540872544088591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_89, prime_t64_521, prime_t64_719, prime_lucas_460540872544088591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361678 : Nat.totient 1182266884102822267511361678 = 363774425877791466926572800 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (15157267744907977788607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_lucas_15157267744907977788607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361679 : Nat.totient 1182266884102822267511361679 = 1182251467550236957608105216 := by
  rw [← show ((([(76697, 1), (664551479, 1), (23195755332433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_76697, prime_lucas_664551479, prime_lucas_23195755332433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361680 : Nat.totient 1182266884102822267511361680 = 472906753641128907004544640 := by
  rw [← show ((([(2, 4), (5, 1), (14778336051285278343892021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_lucas_14778336051285278343892021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361681 : Nat.totient 1182266884102822267511361681 = 788177910387450727738576080 := by
  rw [← show ((([(3, 3), (63831631, 1), (685986895340001613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_lucas_63831631, prime_lucas_685986895340001613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361682 : Nat.totient 1182266884102822267511361682 = 576656819140432210528158720 := by
  rw [← show ((([(2, 1), (41, 2), (9829, 1), (9743417, 1), (3671953652077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_t64_9829, prime_t64_9743417, prime_lucas_3671953652077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361683 : Nat.totient 1182266884102822267511361683 = 1182266879779521307096941000 := by
  rw [← show ((([(273463933, 1), (4323300960140956751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_273463933, prime_lucas_4323300960140956751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361684 : Nat.totient 1182266884102822267511361684 = 335523487722373337663815296 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (149, 1), (94460441363280781999949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_149, prime_lucas_94460441363280781999949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361685 : Nat.totient 1182266884102822267511361685 = 890176686902373699680256000 := by
  rw [← show ((([(5, 1), (17, 1), (1216561, 1), (11433065967029648401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_t64_1216561, prime_lucas_11433065967029648401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361686 : Nat.totient 1182266884102822267511361686 = 576712994242457575088441856 := by
  rw [← show ((([(2, 1), (43, 1), (859, 1), (622577, 1), (8109733, 1), (3169744679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_t64_859, prime_t64_622577, prime_t64_8109733, prime_lucas_3169744679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361687 : Nat.totient 1182266884102822267511361687 = 760999373674466774804208224 := by
  rw [← show ((([(3, 1), (29, 1), (881055049019, 1), (15423865449779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_lucas_881055049019, prime_lucas_15423865449779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361688 : Nat.totient 1182266884102822267511361688 = 536580606310624334606400000 := by
  rw [← show ((([(2, 3), (11, 1), (661, 1), (1276501, 1), (70401439, 1), (226166719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_661, prime_t64_1276501, prime_lucas_70401439, prime_lucas_226166719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361689 : Nat.totient 1182266884102822267511361689 = 1182233813869473880568958720 := by
  rw [← show ((([(36073, 1), (7478579, 1), (8724377, 1), (502319171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_36073, prime_t64_7478579, prime_t64_8724377, prime_lucas_502319171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361690 : Nat.totient 1182266884102822267511361690 = 315094344506965452389292288 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1783, 1), (79467359, 1), (92711347287353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_1783, prime_lucas_79467359, prime_lucas_92711347287353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361691 : Nat.totient 1182266884102822267511361691 = 935419952257178057811187200 := by
  rw [← show ((([(7, 1), (13, 1), (12991943781349695247377601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_lucas_12991943781349695247377601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361692 : Nat.totient 1182266884102822267511361692 = 565430608923219937710935232 := by
  rw [← show ((([(2, 2), (23, 2), (409993, 1), (1362772683724253759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_409993, prime_lucas_1362772683724253759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_1182266884102822267511361693 : Nat.totient 1182266884102822267511361693 = 762671895021725960773370880 := by
  rw [← show ((([(3, 1), (31, 2), (12497, 1), (38329, 1), (856125876868967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_t64_12497, prime_t64_38329, prime_lucas_856125876868967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723201 : Nat.totient 2364533768205644535022723201 = 2364522518859718621007607552 := by
  rw [← show ((([(210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_210193, prime_lucas_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723202 : Nat.totient 2364533768205644535022723202 = 1170554827853295639500976192 := by
  rw [← show ((([(2, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_103, prime_t64_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723203 : Nat.totient 2364533768205644535022723203 = 1571549729260898912144256000 := by
  rw [← show ((([(3, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_421, prime_t64_1483, prime_t64_2072201, prime_t64_2567179, prime_lucas_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723204 : Nat.totient 2364533768205644535022723204 = 1182266883135824490764412200 := by
  rw [← show ((([(2, 2), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723205 : Nat.totient 2364533768205644535022723205 = 1883275367375349618397538112 := by
  rw [← show ((([(5, 1), (239, 1), (4327, 1), (1214459, 1), (376537177183483, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_239, prime_t64_4327, prime_t64_1214459, prime_lucas_376537177183483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723206 : Nat.totient 2364533768205644535022723206 = 788177922735214845007574400 := by
  rw [← show ((([(2, 1), (3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723207 : Nat.totient 2364533768205644535022723207 = 2026722447682971779648341752 := by
  rw [← show ((([(7, 1), (97523, 1), (3463701263446490329787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_97523, prime_lucas_3463701263446490329787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723208 : Nat.totient 2364533768205644535022723208 = 1182266827618099149325191168 := by
  rw [← show ((([(2, 3), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723209 : Nat.totient 2364533768205644535022723209 = 1548204829647044226382771200 := by
  rw [← show ((([(3, 2), (67, 1), (491, 1), (1061, 1), (9492089, 1), (792993323477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_67, prime_t64_491, prime_t64_1061, prime_t64_9492089, prime_lucas_792993323477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723210 : Nat.totient 2364533768205644535022723210 = 945813505771568331823918608 := by
  rw [← show ((([(2, 1), (5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723211 : Nat.totient 2364533768205644535022723211 = 2149576152914222304566112000 := by
  rw [← show ((([(11, 1), (214957615291422230456611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11, prime_lucas_214957615291422230456611201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723212 : Nat.totient 2364533768205644535022723212 = 786233414280496855721553792 := by
  rw [← show ((([(2, 2), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_409, prime_t64_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723213 : Nat.totient 2364533768205644535022723213 = 2182646555266243577460304944 := by
  rw [← show ((([(13, 1), (4887540332063, 1), (37214467928927, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_13, prime_lucas_4887540332063, prime_lucas_37214467928927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723214 : Nat.totient 2364533768205644535022723214 = 1011173411801001135106919520 := by
  rw [← show ((([(2, 1), (7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723215 : Nat.totient 2364533768205644535022723215 = 1261082653069483780238868512 := by
  rw [← show ((([(3, 1), (5, 1), (623279, 1), (252913357496471033039, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_623279, prime_lucas_252913357496471033039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723216 : Nat.totient 2364533768205644535022723216 = 1176077000958651971838301440 := by
  rw [← show ((([(2, 4), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723217 : Nat.totient 2364533768205644535022723217 = 2213650503512042666304430080 := by
  rw [← show ((([(17, 1), (229, 1), (1669, 1), (2963, 1), (108608761, 1), (1130858507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_17, prime_t64_229, prime_t64_1669, prime_t64_2963, prime_lucas_108608761, prime_lucas_1130858507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723218 : Nat.totient 2364533768205644535022723218 = 788177922735214845007574400 := by
  rw [← show ((([(2, 1), (3, 2), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723219 : Nat.totient 2364533768205644535022723219 = 2215720412886444789464064000 := by
  rw [← show ((([(19, 1), (149, 1), (349, 1), (1213, 1), (2897, 1), (6151, 1), (110719776691, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_19, prime_t64_149, prime_t64_349, prime_t64_1213, prime_t64_2897, prime_t64_6151, prime_lucas_110719776691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723220 : Nat.totient 2364533768205644535022723220 = 936449017111146350504048000 := by
  rw [← show ((([(2, 2), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723221 : Nat.totient 2364533768205644535022723221 = 1350749207586578901940666368 := by
  rw [← show ((([(3, 1), (7, 1), (4787, 1), (10337, 1), (269456833, 1), (8444599963, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_4787, prime_t64_10337, prime_lucas_269456833, prime_lucas_8444599963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723222 : Nat.totient 2364533768205644535022723222 = 1074788076457111152283056000 := by
  rw [← show ((([(2, 1), (11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723223 : Nat.totient 2364533768205644535022723223 = 2260548953839384818190783488 := by
  rw [← show ((([(23, 1), (2417, 1), (9343, 1), (1789993, 1), (2543333740247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_23, prime_t64_2417, prime_t64_9343, prime_t64_1789993, prime_lucas_2543333740247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723224 : Nat.totient 2364533768205644535022723224 = 785642884247790019167452160 := by
  rw [← show ((([(2, 3), (3, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_311, prime_t64_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723225 : Nat.totient 2364533768205644535022723225 = 1889718170330302521809688000 := by
  rw [← show ((([(5, 2), (991, 1), (49777621, 1), (1917333766315939, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_991, prime_lucas_49777621, prime_lucas_1917333766315939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723226 : Nat.totient 2364533768205644535022723226 = 1091322450430260586490332224 := by
  rw [← show ((([(2, 1), (13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_1319293, prime_lucas_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723227 : Nat.totient 2364533768205644535022723227 = 1575791914973298118263498240 := by
  rw [← show ((([(3, 4), (3511, 1), (13709, 1), (606490351024352033, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_3511, prime_t64_13709, prime_lucas_606490351024352033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723228 : Nat.totient 2364533768205644535022723228 = 1009659458204822863872000000 := by
  rw [← show ((([(2, 2), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_433, prime_t64_751, prime_t64_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723229 : Nat.totient 2364533768205644535022723229 = 2280407113088797134610022400 := by
  rw [← show ((([(29, 1), (1229, 1), (3121, 1), (911749, 1), (23314525201361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_29, prime_t64_1229, prime_t64_3121, prime_t64_911749, prime_lucas_23314525201361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723230 : Nat.totient 2364533768205644535022723230 = 630542218085853059114011296 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_5250043, prime_lucas_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723231 : Nat.totient 2364533768205644535022723231 = 2288248379168577413923676160 := by
  rw [← show ((([(31, 1), (241513, 1), (3623449, 1), (87160790647873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_31, prime_t64_241513, prime_t64_3623449, prime_lucas_87160790647873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723232 : Nat.totient 2364533768205644535022723232 = 1182266884096899802201308672 := by
  rw [← show ((([(2, 5), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723233 : Nat.totient 2364533768205644535022723233 = 1433050768347588254158216640 := by
  rw [← show ((([(3, 1), (11, 1), (5471890517, 1), (13094658639069053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_11, prime_lucas_5471890517, prime_lucas_13094658639069053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723234 : Nat.totient 2364533768205644535022723234 = 1112721773273244487069516800 := by
  rw [← show ((([(2, 1), (17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_lucas_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723235 : Nat.totient 2364533768205644535022723235 = 1621394583912441966872724480 := by
  rw [← show ((([(5, 1), (7, 1), (67558107663018415286363521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_7, prime_lucas_67558107663018415286363521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723236 : Nat.totient 2364533768205644535022723236 = 786744008195367107837952000 := by
  rw [← show ((([(2, 2), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_1051, prime_t64_1153, prime_t64_940369, prime_t64_6947861, prime_t64_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723237 : Nat.totient 2364533768205644535022723237 = 2300627450146032520562649600 := by
  rw [← show ((([(37, 1), (63906318059612014460073601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_37, prime_lucas_63906318059612014460073601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723238 : Nat.totient 2364533768205644535022723238 = 1118619131698437065522004456 := by
  rw [← show ((([(2, 1), (19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_787, prime_lucas_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723239 : Nat.totient 2364533768205644535022723239 = 1455097703511165867706291200 := by
  rw [← show ((([(3, 1), (13, 1), (60629070979631911154428801, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_13, prime_lucas_60629070979631911154428801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723240 : Nat.totient 2364533768205644535022723240 = 938909759053920165731648512 := by
  rw [← show ((([(2, 3), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_137, prime_lucas_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723241 : Nat.totient 2364533768205644535022723241 = 2303409922697810351939512320 := by
  rw [← show ((([(41, 1), (997, 1), (2909, 1), (6653, 1), (2988857852678629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_41, prime_t64_997, prime_t64_2909, prime_t64_6653, prime_lucas_2988857852678629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723242 : Nat.totient 2364533768205644535022723242 = 674536901859503806414070064 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (647, 1), (87014564223362204129783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_t64_647, prime_lucas_87014564223362204129783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723243 : Nat.totient 2364533768205644535022723243 = 2309544610805513266766380800 := by
  rw [← show ((([(43, 1), (54989157400131268256342401, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_43, prime_lucas_54989157400131268256342401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723244 : Nat.totient 2364533768205644535022723244 = 1074771630455103695420275200 := by
  rw [← show ((([(2, 2), (11, 1), (65353, 1), (10672982981, 1), (77044474757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_65353, prime_lucas_10672982981, prime_lucas_77044474757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723245 : Nat.totient 2364533768205644535022723245 = 1243809543823243152669485568 := by
  rw [← show ((([(3, 2), (5, 1), (73, 1), (719797189712524972609657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_t64_73, prime_lucas_719797189712524972609657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723246 : Nat.totient 2364533768205644535022723246 = 1130720846877228034389940000 := by
  rw [← show ((([(2, 1), (23, 1), (7901, 1), (6505873687440897781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_7901, prime_lucas_6505873687440897781301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723247 : Nat.totient 2364533768205644535022723247 = 2267632090772421257840104800 := by
  rw [← show ((([(47, 1), (71, 1), (163, 1), (302255347, 1), (14382279258671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_47, prime_t64_71, prime_t64_163, prime_lucas_302255347, prime_lucas_14382279258671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723248 : Nat.totient 2364533768205644535022723248 = 781019988207957655297674240 := by
  rw [← show ((([(2, 4), (3, 1), (113, 1), (4271, 1), (102069566040058032487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_113, prime_t64_4271, prime_lucas_102069566040058032487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723249 : Nat.totient 2364533768205644535022723249 = 2026743229890552458590905348 := by
  rw [← show ((([(7, 3), (6893684455410042376159543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_lucas_6893684455410042376159543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723250 : Nat.totient 2364533768205644535022723250 = 945807159723492911330304000 := by
  rw [← show ((([(2, 1), (5, 3), (149059, 1), (407047681, 1), (155884173167, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_149059, prime_lucas_407047681, prime_lucas_155884173167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723251 : Nat.totient 2364533768205644535022723251 = 1483628806582054132482157056 := by
  rw [← show ((([(3, 1), (17, 1), (7679389, 1), (47489747, 1), (127130226647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_17, prime_t64_7679389, prime_lucas_47489747, prime_lucas_127130226647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723252 : Nat.totient 2364533768205644535022723252 = 1091323066144279598269230240 := by
  rw [← show ((([(2, 2), (13, 2), (5160187, 1), (677849662823399071, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_13, prime_t64_5160187, prime_lucas_677849662823399071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723253 : Nat.totient 2364533768205644535022723253 = 2281734195408164757239316480 := by
  rw [← show ((([(53, 1), (83, 1), (317, 1), (761, 1), (945103, 1), (2357591178977, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_53, prime_t64_83, prime_t64_317, prime_t64_761, prime_t64_945103, prime_lucas_2357591178977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723254 : Nat.totient 2364533768205644535022723254 = 788177922734890937629881576 := by
  rw [← show ((([(2, 1), (3, 3), (2901032068267, 1), (15093822248003, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_2901032068267, prime_lucas_15093822248003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723255 : Nat.totient 2364533768205644535022723255 = 1719660922331377843652889600 := by
  rw [← show ((([(5, 1), (11, 1), (42991523058284446091322241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_11, prime_lucas_42991523058284446091322241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723256 : Nat.totient 2364533768205644535022723256 = 1003900375594818938560390272 := by
  rw [← show ((([(2, 3), (7, 1), (107, 1), (2106407, 1), (187340392836749749, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_7, prime_t64_107, prime_t64_2106407, prime_lucas_187340392836749749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723257 : Nat.totient 2364533768205644535022723257 = 1493389748340407074751193600 := by
  rw [← show ((([(3, 1), (19, 1), (41483048565011307631977601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_19, prime_lucas_41483048565011307631977601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723258 : Nat.totient 2364533768205644535022723258 = 1141213757073801325196800000 := by
  rw [← show ((([(2, 1), (29, 1), (4001, 1), (10189408545301797546401, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_29, prime_t64_4001, prime_lucas_10189408545301797546401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723259 : Nat.totient 2364533768205644535022723259 = 2303075763458313867327628800 := by
  rw [← show ((([(59, 1), (227, 1), (283, 1), (883, 1), (10789, 1), (16603, 1), (3944143901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_59, prime_t64_227, prime_t64_283, prime_t64_883, prime_t64_10789, prime_t64_16603, prime_lucas_3944143901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723260 : Nat.totient 2364533768205644535022723260 = 630542285818237376761379904 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (12040159, 1), (3273120906190752319, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_12040159, prime_lucas_3273120906190752319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723261 : Nat.totient 2364533768205644535022723261 = 2296330781066298357388937280 := by
  rw [← show ((([(61, 1), (79, 1), (8897487107, 1), (55146915580517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_61, prime_t64_79, prime_lucas_8897487107, prime_lucas_55146915580517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723262 : Nat.totient 2364533768205644535022723262 = 1143324662113825832429601120 := by
  rw [← show ((([(2, 1), (31, 1), (1423, 1), (3748763, 1), (4597727, 1), (1554954787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_31, prime_t64_1423, prime_t64_3748763, prime_t64_4597727, prime_lucas_1554954787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723263 : Nat.totient 2364533768205644535022723263 = 1351162060446675263551488000 := by
  rw [← show ((([(3, 2), (7, 1), (16364731, 1), (132858611, 1), (17262607361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_7, prime_t64_16364731, prime_lucas_132858611, prime_lucas_17262607361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723264 : Nat.totient 2364533768205644535022723264 = 1172741590682249430360960000 := by
  rw [← show ((([(2, 6), (139, 1), (1151, 1), (1214653051, 1), (190117973909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_139, prime_t64_1151, prime_lucas_1214653051, prime_lucas_190117973909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723265 : Nat.totient 2364533768205644535022723265 = 1726269966813902024635760640 := by
  rw [← show ((([(5, 1), (13, 1), (89, 1), (8093, 1), (117833, 1), (428613338361941, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_13, prime_t64_89, prime_t64_8093, prime_t64_117833, prime_lucas_428613338361941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723266 : Nat.totient 2364533768205644535022723266 = 716525294224298420086473600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (11633099, 1), (25210021, 1), (11105555029, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_11, prime_t64_11633099, prime_t64_25210021, prime_lucas_11105555029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723267 : Nat.totient 2364533768205644535022723267 = 2364201879504187760352737280 := by
  rw [← show ((([(7669, 1), (106721, 1), (1674649, 1), (1725174786767, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7669, prime_t64_106721, prime_t64_1674649, prime_lucas_1725174786767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723268 : Nat.totient 2364533768205644535022723268 = 1110491869354908485801911296 := by
  rw [← show ((([(2, 2), (17, 1), (499, 1), (1965292547, 1), (35457560705417, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_17, prime_t64_499, prime_lucas_1965292547, prime_lucas_35457560705417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723269 : Nat.totient 2364533768205644535022723269 = 1507451506144585024742545728 := by
  rw [← show ((([(3, 1), (23, 1), (4133, 1), (654163, 1), (12674914783893119, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_23, prime_t64_4133, prime_t64_654163, prime_lucas_12674914783893119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723270 : Nat.totient 2364533768205644535022723270 = 807189700743848057422556160 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (233, 1), (28621, 1), (5065318471177066877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_7, prime_t64_233, prime_t64_28621, prime_lucas_5065318471177066877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723271 : Nat.totient 2364533768205644535022723271 = 2364533316521453293068071472 := by
  rw [← show ((([(5234927, 1), (451684191241949416873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5234927, prime_lucas_451684191241949416873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723272 : Nat.totient 2364533768205644535022723272 = 788177922735214845007574400 := by
  rw [← show ((([(2, 3), (3, 2), (32840746780633951875315601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_lucas_32840746780633951875315601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723273 : Nat.totient 2364533768205644535022723273 = 2364533768205644535022723272 := by
  rw [← show ((([(2364533768205644535022723273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_2364533768205644535022723273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723274 : Nat.totient 2364533768205644535022723274 = 1146690578612362057176672000 := by
  rw [← show ((([(2, 1), (37, 1), (431, 1), (1973, 1), (3187, 1), (90931, 1), (129662805691, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_37, prime_t64_431, prime_t64_1973, prime_t64_3187, prime_t64_90931, prime_lucas_129662805691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723275 : Nat.totient 2364533768205644535022723275 = 1261084676362873586755338240 := by
  rw [← show ((([(3, 1), (5, 2), (93646621249, 1), (336660484798273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_5, prime_lucas_93646621249, prime_lucas_336660484798273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723276 : Nat.totient 2364533768205644535022723276 = 1103325261830039656469698560 := by
  rw [← show ((([(2, 2), (19, 1), (67, 1), (442529322881, 1), (1049337207563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_19, prime_t64_67, prime_lucas_442529322881, prime_lucas_1049337207563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723277 : Nat.totient 2364533768205644535022723277 = 1835644425855586545800466240 := by
  rw [← show ((([(7, 1), (11, 1), (269, 1), (114156991657685730460229, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_11, prime_t64_269, prime_lucas_114156991657685730460229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723278 : Nat.totient 2364533768205644535022723278 = 727531201799207407228982400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (41221, 1), (735414848980275965581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_13, prime_t64_41221, prime_lucas_735414848980275965581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723279 : Nat.totient 2364533768205644535022723279 = 2364533560485727610753880000 := by
  rw [← show ((([(11383279, 1), (207719916924257460001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_11383279, prime_lucas_207719916924257460001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723280 : Nat.totient 2364533768205644535022723280 = 942724742500807432574865408 := by
  rw [← show ((([(2, 4), (5, 1), (307, 1), (120293, 1), (9238457, 1), (86631804463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_5, prime_t64_307, prime_t64_120293, prime_t64_9238457, prime_lucas_86631804463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723281 : Nat.totient 2364533768205644535022723281 = 1573023080868009061182586560 := by
  rw [← show ((([(3, 3), (479, 1), (44741, 1), (235679, 1), (17338825249063, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_479, prime_t64_44741, prime_t64_235679, prime_lucas_17338825249063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723282 : Nat.totient 2364533768205644535022723282 = 1146211887247010197130649600 := by
  rw [← show ((([(2, 1), (41, 1), (167, 1), (3769, 1), (138977, 1), (329644722325231, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_41, prime_t64_167, prime_t64_3769, prime_t64_138977, prime_lucas_329644722325231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723283 : Nat.totient 2364533768205644535022723283 = 2362366459527179232974122080 := by
  rw [← show ((([(1091, 1), (2167308678465302048600113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_1091, prime_lucas_2167308678465302048600113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723284 : Nat.totient 2364533768205644535022723284 = 675581063858633765679149952 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (64596797, 1), (398497559, 1), (1093527187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_7, prime_lucas_64596797, prime_lucas_398497559, prime_lucas_1093527187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723285 : Nat.totient 2364533768205644535022723285 = 1768058294719534393813106688 := by
  rw [← show ((([(5, 1), (17, 1), (193, 1), (1093, 1), (1373, 1), (11113, 1), (509833, 1), (16951937, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_5, prime_t64_17, prime_t64_193, prime_t64_1093, prime_t64_1373, prime_t64_11113, prime_t64_509833, prime_t64_16951937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723286 : Nat.totient 2364533768205644535022723286 = 1142867436261497695543447296 := by
  rw [← show ((([(2, 1), (43, 1), (97, 1), (87628772527, 1), (3234659767279, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_43, prime_t64_97, prime_lucas_87628772527, prime_lucas_3234659767279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723287 : Nat.totient 2364533768205644535022723287 = 1521998747350114559674557024 := by
  rw [← show ((([(3, 1), (29, 1), (3310450221739, 1), (8209925309059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_29, prime_lucas_3310450221739, prime_lucas_8209925309059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723288 : Nat.totient 2364533768205644535022723288 = 1074786571469963536258500000 := by
  rw [← show ((([(2, 3), (11, 1), (714151, 1), (37624678690399899751, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_11, prime_t64_714151, prime_lucas_37624678690399899751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723289 : Nat.totient 2364533768205644535022723289 = 2364518250120556727251006176 := by
  rw [← show ((([(152377, 1), (5512921759, 1), (2814778809023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_152377, prime_lucas_5512921759, prime_lucas_2814778809023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723290 : Nat.totient 2364533768205644535022723290 = 627605493218555954201814528 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (223, 1), (5743, 1), (20514424207990512529, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_3, prime_t64_5, prime_t64_223, prime_t64_5743, prime_lucas_20514424207990512529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723291 : Nat.totient 2364533768205644535022723291 = 1870052106219864191237403648 := by
  rw [← show ((([(7, 1), (13, 1), (2377, 1), (2970893, 1), (18689423, 1), (196875667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_7, prime_t64_13, prime_t64_2377, prime_t64_2970893, prime_t64_18689423, prime_lucas_196875667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723292 : Nat.totient 2364533768205644535022723292 = 1120489077235064103552845376 := by
  rw [← show ((([(2, 2), (23, 1), (109, 1), (235793155983809786101189, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_2, prime_t64_23, prime_t64_109, prime_lucas_235793155983809786101189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t64_2364533768205644535022723293 : Nat.totient 2364533768205644535022723293 = 1525505572965657824349000000 := by
  rw [← show ((([(3, 1), (31, 1), (18173501, 1), (1399020160275178901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2364533768205644535022723293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t64_3, prime_t64_31, prime_t64_18173501, prime_lucas_1399020160275178901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-eighth finite diagonal certificate -/

theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t64_1182266884102822267511361601, phi_t64_1182266884102822267511361602, phi_t64_1182266884102822267511361603, phi_t64_1182266884102822267511361604, phi_t64_1182266884102822267511361605, phi_t64_1182266884102822267511361606, phi_t64_1182266884102822267511361607, phi_t64_1182266884102822267511361608, phi_t64_1182266884102822267511361609, phi_t64_1182266884102822267511361610, phi_t64_1182266884102822267511361611, phi_t64_1182266884102822267511361612, phi_t64_1182266884102822267511361613, phi_t64_1182266884102822267511361614, phi_t64_1182266884102822267511361615, phi_t64_1182266884102822267511361616, phi_t64_1182266884102822267511361617, phi_t64_1182266884102822267511361618, phi_t64_1182266884102822267511361619, phi_t64_1182266884102822267511361620, phi_t64_1182266884102822267511361621, phi_t64_1182266884102822267511361622, phi_t64_1182266884102822267511361623, phi_t64_1182266884102822267511361624, phi_t64_1182266884102822267511361625, phi_t64_1182266884102822267511361626, phi_t64_1182266884102822267511361627, phi_t64_1182266884102822267511361628, phi_t64_1182266884102822267511361629, phi_t64_1182266884102822267511361630, phi_t64_1182266884102822267511361631, phi_t64_1182266884102822267511361632, phi_t64_1182266884102822267511361633, phi_t64_1182266884102822267511361634, phi_t64_1182266884102822267511361635, phi_t64_1182266884102822267511361636, phi_t64_1182266884102822267511361637, phi_t64_1182266884102822267511361638, phi_t64_1182266884102822267511361639, phi_t64_1182266884102822267511361640, phi_t64_1182266884102822267511361641, phi_t64_1182266884102822267511361642, phi_t64_1182266884102822267511361643, phi_t64_1182266884102822267511361644, phi_t64_1182266884102822267511361645, phi_t64_1182266884102822267511361646, phi_t64_1182266884102822267511361647, phi_t64_1182266884102822267511361648, phi_t64_1182266884102822267511361649, phi_t64_1182266884102822267511361650, phi_t64_1182266884102822267511361651, phi_t64_1182266884102822267511361652, phi_t64_1182266884102822267511361653, phi_t64_1182266884102822267511361654, phi_t64_1182266884102822267511361655, phi_t64_1182266884102822267511361656, phi_t64_1182266884102822267511361657, phi_t64_1182266884102822267511361658, phi_t64_1182266884102822267511361659, phi_t64_1182266884102822267511361660, phi_t64_1182266884102822267511361661, phi_t64_1182266884102822267511361662, phi_t64_1182266884102822267511361663, phi_t64_1182266884102822267511361664, phi_t64_1182266884102822267511361665, phi_t64_1182266884102822267511361666, phi_t64_1182266884102822267511361667, phi_t64_1182266884102822267511361668, phi_t64_1182266884102822267511361669, phi_t64_1182266884102822267511361670, phi_t64_1182266884102822267511361671, phi_t64_1182266884102822267511361672, phi_t64_1182266884102822267511361673, phi_t64_1182266884102822267511361674, phi_t64_1182266884102822267511361675, phi_t64_1182266884102822267511361676, phi_t64_1182266884102822267511361677, phi_t64_1182266884102822267511361678, phi_t64_1182266884102822267511361679, phi_t64_1182266884102822267511361680, phi_t64_1182266884102822267511361681, phi_t64_1182266884102822267511361682, phi_t64_1182266884102822267511361683, phi_t64_1182266884102822267511361684, phi_t64_1182266884102822267511361685, phi_t64_1182266884102822267511361686, phi_t64_1182266884102822267511361687, phi_t64_1182266884102822267511361688, phi_t64_1182266884102822267511361689, phi_t64_1182266884102822267511361690, phi_t64_1182266884102822267511361691, phi_t64_1182266884102822267511361692, phi_t64_1182266884102822267511361693, phi_t64_2364533768205644535022723201, phi_t64_2364533768205644535022723202, phi_t64_2364533768205644535022723203, phi_t64_2364533768205644535022723204, phi_t64_2364533768205644535022723205, phi_t64_2364533768205644535022723206, phi_t64_2364533768205644535022723207, phi_t64_2364533768205644535022723208, phi_t64_2364533768205644535022723209, phi_t64_2364533768205644535022723210, phi_t64_2364533768205644535022723211, phi_t64_2364533768205644535022723212, phi_t64_2364533768205644535022723213, phi_t64_2364533768205644535022723214, phi_t64_2364533768205644535022723215, phi_t64_2364533768205644535022723216, phi_t64_2364533768205644535022723217, phi_t64_2364533768205644535022723218, phi_t64_2364533768205644535022723219, phi_t64_2364533768205644535022723220, phi_t64_2364533768205644535022723221, phi_t64_2364533768205644535022723222, phi_t64_2364533768205644535022723223, phi_t64_2364533768205644535022723224, phi_t64_2364533768205644535022723225, phi_t64_2364533768205644535022723226, phi_t64_2364533768205644535022723227, phi_t64_2364533768205644535022723228, phi_t64_2364533768205644535022723229, phi_t64_2364533768205644535022723230, phi_t64_2364533768205644535022723231, phi_t64_2364533768205644535022723232, phi_t64_2364533768205644535022723233, phi_t64_2364533768205644535022723234, phi_t64_2364533768205644535022723235, phi_t64_2364533768205644535022723236, phi_t64_2364533768205644535022723237, phi_t64_2364533768205644535022723238, phi_t64_2364533768205644535022723239, phi_t64_2364533768205644535022723240, phi_t64_2364533768205644535022723241, phi_t64_2364533768205644535022723242, phi_t64_2364533768205644535022723243, phi_t64_2364533768205644535022723244, phi_t64_2364533768205644535022723245, phi_t64_2364533768205644535022723246, phi_t64_2364533768205644535022723247, phi_t64_2364533768205644535022723248, phi_t64_2364533768205644535022723249, phi_t64_2364533768205644535022723250, phi_t64_2364533768205644535022723251, phi_t64_2364533768205644535022723252, phi_t64_2364533768205644535022723253, phi_t64_2364533768205644535022723254, phi_t64_2364533768205644535022723255, phi_t64_2364533768205644535022723256, phi_t64_2364533768205644535022723257, phi_t64_2364533768205644535022723258, phi_t64_2364533768205644535022723259, phi_t64_2364533768205644535022723260, phi_t64_2364533768205644535022723261, phi_t64_2364533768205644535022723262, phi_t64_2364533768205644535022723263, phi_t64_2364533768205644535022723264, phi_t64_2364533768205644535022723265, phi_t64_2364533768205644535022723266, phi_t64_2364533768205644535022723267, phi_t64_2364533768205644535022723268, phi_t64_2364533768205644535022723269, phi_t64_2364533768205644535022723270, phi_t64_2364533768205644535022723271, phi_t64_2364533768205644535022723272, phi_t64_2364533768205644535022723273, phi_t64_2364533768205644535022723274, phi_t64_2364533768205644535022723275, phi_t64_2364533768205644535022723276, phi_t64_2364533768205644535022723277, phi_t64_2364533768205644535022723278, phi_t64_2364533768205644535022723279, phi_t64_2364533768205644535022723280, phi_t64_2364533768205644535022723281, phi_t64_2364533768205644535022723282, phi_t64_2364533768205644535022723283, phi_t64_2364533768205644535022723284, phi_t64_2364533768205644535022723285, phi_t64_2364533768205644535022723286, phi_t64_2364533768205644535022723287, phi_t64_2364533768205644535022723288, phi_t64_2364533768205644535022723289, phi_t64_2364533768205644535022723290, phi_t64_2364533768205644535022723291, phi_t64_2364533768205644535022723292, phi_t64_2364533768205644535022723293]

def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]

def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0

/-- All 28 imported scales through t=64 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t64 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT64, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t47
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t49
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t53
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t59
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t61
  · simpa [diagonalPincerKillDepthThroughT64] using certifiedKill_diagonal_t64

#print axioms certifiedKill_diagonal_all_imported_through_t64

end TotientTailPeriodKiller
end Erdos249257
