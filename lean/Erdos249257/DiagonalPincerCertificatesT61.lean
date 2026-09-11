import Erdos249257.DiagonalPincerCertificatesT59
import Erdos249257.DiagonalPincerPrimeCertificates.ClosureT64

/-!
# The t=61 diagonal-pincer certificate

This generated extension consumes 173 new large-prime Lucas roots
and 1069 recursive Pratt dependencies, reuses 0 earlier certificates,
reconstructs all 188 Euler totients in the t=61 window, and proves the
twenty-seventh finite diagonal kill without `native_decide`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Prime leaves used by the t=61 window -/

private theorem prime_t61_2 : Nat.Prime 2 := by norm_num
private theorem prime_t61_3 : Nat.Prime 3 := by norm_num
private theorem prime_t61_5 : Nat.Prime 5 := by norm_num
private theorem prime_t61_7 : Nat.Prime 7 := by norm_num
private theorem prime_t61_11 : Nat.Prime 11 := by norm_num
private theorem prime_t61_13 : Nat.Prime 13 := by norm_num
private theorem prime_t61_17 : Nat.Prime 17 := by norm_num
private theorem prime_t61_19 : Nat.Prime 19 := by norm_num
private theorem prime_t61_23 : Nat.Prime 23 := by norm_num
private theorem prime_t61_29 : Nat.Prime 29 := by norm_num
private theorem prime_t61_31 : Nat.Prime 31 := by norm_num
private theorem prime_t61_37 : Nat.Prime 37 := by norm_num
private theorem prime_t61_41 : Nat.Prime 41 := by norm_num
private theorem prime_t61_43 : Nat.Prime 43 := by norm_num
private theorem prime_t61_47 : Nat.Prime 47 := by norm_num
private theorem prime_t61_53 : Nat.Prime 53 := by norm_num
private theorem prime_t61_59 : Nat.Prime 59 := by norm_num
private theorem prime_t61_61 : Nat.Prime 61 := by norm_num
private theorem prime_t61_67 : Nat.Prime 67 := by norm_num
private theorem prime_t61_71 : Nat.Prime 71 := by norm_num
private theorem prime_t61_73 : Nat.Prime 73 := by norm_num
private theorem prime_t61_79 : Nat.Prime 79 := by norm_num
private theorem prime_t61_83 : Nat.Prime 83 := by norm_num
private theorem prime_t61_89 : Nat.Prime 89 := by norm_num
private theorem prime_t61_97 : Nat.Prime 97 := by norm_num
private theorem prime_t61_101 : Nat.Prime 101 := by norm_num
private theorem prime_t61_103 : Nat.Prime 103 := by norm_num
private theorem prime_t61_107 : Nat.Prime 107 := by norm_num
private theorem prime_t61_109 : Nat.Prime 109 := by norm_num
private theorem prime_t61_113 : Nat.Prime 113 := by norm_num
private theorem prime_t61_127 : Nat.Prime 127 := by norm_num
private theorem prime_t61_131 : Nat.Prime 131 := by norm_num
private theorem prime_t61_137 : Nat.Prime 137 := by norm_num
private theorem prime_t61_139 : Nat.Prime 139 := by norm_num
private theorem prime_t61_149 : Nat.Prime 149 := by norm_num
private theorem prime_t61_157 : Nat.Prime 157 := by norm_num
private theorem prime_t61_167 : Nat.Prime 167 := by norm_num
private theorem prime_t61_173 : Nat.Prime 173 := by norm_num
private theorem prime_t61_179 : Nat.Prime 179 := by norm_num
private theorem prime_t61_181 : Nat.Prime 181 := by norm_num
private theorem prime_t61_191 : Nat.Prime 191 := by norm_num
private theorem prime_t61_197 : Nat.Prime 197 := by norm_num
private theorem prime_t61_199 : Nat.Prime 199 := by norm_num
private theorem prime_t61_223 : Nat.Prime 223 := by norm_num
private theorem prime_t61_233 : Nat.Prime 233 := by norm_num
private theorem prime_t61_239 : Nat.Prime 239 := by norm_num
private theorem prime_t61_251 : Nat.Prime 251 := by norm_num
private theorem prime_t61_257 : Nat.Prime 257 := by norm_num
private theorem prime_t61_263 : Nat.Prime 263 := by norm_num
private theorem prime_t61_271 : Nat.Prime 271 := by norm_num
private theorem prime_t61_307 : Nat.Prime 307 := by norm_num
private theorem prime_t61_311 : Nat.Prime 311 := by norm_num
private theorem prime_t61_347 : Nat.Prime 347 := by norm_num
private theorem prime_t61_349 : Nat.Prime 349 := by norm_num
private theorem prime_t61_359 : Nat.Prime 359 := by norm_num
private theorem prime_t61_383 : Nat.Prime 383 := by norm_num
private theorem prime_t61_409 : Nat.Prime 409 := by norm_num
private theorem prime_t61_431 : Nat.Prime 431 := by norm_num
private theorem prime_t61_433 : Nat.Prime 433 := by norm_num
private theorem prime_t61_439 : Nat.Prime 439 := by norm_num
private theorem prime_t61_461 : Nat.Prime 461 := by norm_num
private theorem prime_t61_467 : Nat.Prime 467 := by norm_num
private theorem prime_t61_487 : Nat.Prime 487 := by norm_num
private theorem prime_t61_499 : Nat.Prime 499 := by norm_num
private theorem prime_t61_521 : Nat.Prime 521 := by norm_num
private theorem prime_t61_563 : Nat.Prime 563 := by norm_num
private theorem prime_t61_607 : Nat.Prime 607 := by norm_num
private theorem prime_t61_617 : Nat.Prime 617 := by norm_num
private theorem prime_t61_641 : Nat.Prime 641 := by norm_num
private theorem prime_t61_647 : Nat.Prime 647 := by norm_num
private theorem prime_t61_659 : Nat.Prime 659 := by norm_num
private theorem prime_t61_661 : Nat.Prime 661 := by norm_num
private theorem prime_t61_673 : Nat.Prime 673 := by norm_num
private theorem prime_t61_683 : Nat.Prime 683 := by norm_num
private theorem prime_t61_719 : Nat.Prime 719 := by norm_num
private theorem prime_t61_743 : Nat.Prime 743 := by norm_num
private theorem prime_t61_751 : Nat.Prime 751 := by norm_num
private theorem prime_t61_787 : Nat.Prime 787 := by norm_num
private theorem prime_t61_859 : Nat.Prime 859 := by norm_num
private theorem prime_t61_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_t61_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_t61_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_t61_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_t61_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_t61_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_t61_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_t61_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_t61_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_t61_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_t61_1613 : Nat.Prime 1613 := by norm_num
private theorem prime_t61_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_t61_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_t61_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_t61_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_t61_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_t61_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_t61_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_t61_2251 : Nat.Prime 2251 := by norm_num
private theorem prime_t61_2281 : Nat.Prime 2281 := by norm_num
private theorem prime_t61_2287 : Nat.Prime 2287 := by norm_num
private theorem prime_t61_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_t61_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_t61_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_t61_3187 : Nat.Prime 3187 := by norm_num
private theorem prime_t61_3217 : Nat.Prime 3217 := by norm_num
private theorem prime_t61_3697 : Nat.Prime 3697 := by norm_num
private theorem prime_t61_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_t61_3769 : Nat.Prime 3769 := by norm_num
private theorem prime_t61_4001 : Nat.Prime 4001 := by norm_num
private theorem prime_t61_4271 : Nat.Prime 4271 := by norm_num
private theorem prime_t61_4933 : Nat.Prime 4933 := by norm_num
private theorem prime_t61_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_t61_5059 : Nat.Prime 5059 := by norm_num
private theorem prime_t61_5503 : Nat.Prime 5503 := by norm_num
private theorem prime_t61_5743 : Nat.Prime 5743 := by norm_num
private theorem prime_t61_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_t61_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_t61_7901 : Nat.Prime 7901 := by norm_num
private theorem prime_t61_8543 : Nat.Prime 8543 := by norm_num
private theorem prime_t61_9829 : Nat.Prime 9829 := by norm_num
private theorem prime_t61_10069 : Nat.Prime 10069 := by norm_num
private theorem prime_t61_10709 : Nat.Prime 10709 := by norm_num
private theorem prime_t61_12497 : Nat.Prime 12497 := by norm_num
private theorem prime_t61_15511 : Nat.Prime 15511 := by norm_num
private theorem prime_t61_16993 : Nat.Prime 16993 := by norm_num
private theorem prime_t61_17921 : Nat.Prime 17921 := by norm_num
private theorem prime_t61_19759 : Nat.Prime 19759 := by norm_num
private theorem prime_t61_21247 : Nat.Prime 21247 := by norm_num
private theorem prime_t61_24821 : Nat.Prime 24821 := by norm_num
private theorem prime_t61_28621 : Nat.Prime 28621 := by norm_num
private theorem prime_t61_30491 : Nat.Prime 30491 := by norm_num
private theorem prime_t61_31337 : Nat.Prime 31337 := by norm_num
private theorem prime_t61_31397 : Nat.Prime 31397 := by norm_num
private theorem prime_t61_34613 : Nat.Prime 34613 := by norm_num
private theorem prime_t61_36073 : Nat.Prime 36073 := by norm_num
private theorem prime_t61_38329 : Nat.Prime 38329 := by norm_num
private theorem prime_t61_39551 : Nat.Prime 39551 := by norm_num
private theorem prime_t61_41221 : Nat.Prime 41221 := by norm_num
private theorem prime_t61_41641 : Nat.Prime 41641 := by norm_num
private theorem prime_t61_44959 : Nat.Prime 44959 := by norm_num
private theorem prime_t61_45127 : Nat.Prime 45127 := by norm_num
private theorem prime_t61_48337 : Nat.Prime 48337 := by norm_num
private theorem prime_t61_52453 : Nat.Prime 52453 := by norm_num
private theorem prime_t61_54217 : Nat.Prime 54217 := by norm_num
private theorem prime_t61_58231 : Nat.Prime 58231 := by norm_num
private theorem prime_t61_65353 : Nat.Prime 65353 := by norm_num
private theorem prime_t61_71143 : Nat.Prime 71143 := by norm_num
private theorem prime_t61_76697 : Nat.Prime 76697 := by norm_num
private theorem prime_t61_77477 : Nat.Prime 77477 := by norm_num
private theorem prime_t61_81883 : Nat.Prime 81883 := by norm_num
private theorem prime_t61_89759 : Nat.Prime 89759 := by norm_num
private theorem prime_t61_90931 : Nat.Prime 90931 := by norm_num
private theorem prime_t61_94111 : Nat.Prime 94111 := by norm_num
private theorem prime_t61_95401 : Nat.Prime 95401 := by norm_num
private theorem prime_t61_116689 : Nat.Prime 116689 := by norm_num
private theorem prime_t61_120293 : Nat.Prime 120293 := by norm_num
private theorem prime_t61_125029 : Nat.Prime 125029 := by norm_num
private theorem prime_t61_138977 : Nat.Prime 138977 := by norm_num
private theorem prime_t61_149059 : Nat.Prime 149059 := by norm_num
private theorem prime_t61_174749 : Nat.Prime 174749 := by norm_num
private theorem prime_t61_188843 : Nat.Prime 188843 := by norm_num
private theorem prime_t61_216371 : Nat.Prime 216371 := by norm_num
private theorem prime_t61_222461 : Nat.Prime 222461 := by norm_num
private theorem prime_t61_272659 : Nat.Prime 272659 := by norm_num
private theorem prime_t61_293957 : Nat.Prime 293957 := by norm_num
private theorem prime_t61_309667 : Nat.Prime 309667 := by norm_num
private theorem prime_t61_315547 : Nat.Prime 315547 := by norm_num
private theorem prime_t61_350737 : Nat.Prime 350737 := by norm_num
private theorem prime_t61_409993 : Nat.Prime 409993 := by norm_num
private theorem prime_t61_418709 : Nat.Prime 418709 := by norm_num
private theorem prime_t61_530333 : Nat.Prime 530333 := by norm_num
private theorem prime_t61_537037 : Nat.Prime 537037 := by norm_num
private theorem prime_t61_582643 : Nat.Prime 582643 := by norm_num
private theorem prime_t61_622577 : Nat.Prime 622577 := by norm_num
private theorem prime_t61_671189 : Nat.Prime 671189 := by norm_num
private theorem prime_t61_714151 : Nat.Prime 714151 := by norm_num
private theorem prime_t61_719057 : Nat.Prime 719057 := by norm_num
private theorem prime_t61_933607 : Nat.Prime 933607 := by norm_num
private theorem prime_t61_940369 : Nat.Prime 940369 := by norm_num
private theorem prime_t61_1115447 : Nat.Prime 1115447 := by norm_num
private theorem prime_t61_1216561 : Nat.Prime 1216561 := by norm_num
private theorem prime_t61_1276501 : Nat.Prime 1276501 := by norm_num
private theorem prime_t61_1319293 : Nat.Prime 1319293 := by norm_num
private theorem prime_t61_1632209 : Nat.Prime 1632209 := by norm_num
private theorem prime_t61_2106407 : Nat.Prime 2106407 := by norm_num
private theorem prime_t61_2396833 : Nat.Prime 2396833 := by norm_num
private theorem prime_t61_2450117 : Nat.Prime 2450117 := by norm_num
private theorem prime_t61_2711039 : Nat.Prime 2711039 := by norm_num
private theorem prime_t61_2887697 : Nat.Prime 2887697 := by norm_num
private theorem prime_t61_3701417 : Nat.Prime 3701417 := by norm_num
private theorem prime_t61_3748763 : Nat.Prime 3748763 := by norm_num
private theorem prime_t61_4107799 : Nat.Prime 4107799 := by norm_num
private theorem prime_t61_4597727 : Nat.Prime 4597727 := by norm_num
private theorem prime_t61_5160187 : Nat.Prime 5160187 := by norm_num
private theorem prime_t61_5250043 : Nat.Prime 5250043 := by norm_num
private theorem prime_t61_6141409 : Nat.Prime 6141409 := by norm_num
private theorem prime_t61_6947861 : Nat.Prime 6947861 := by norm_num
private theorem prime_t61_7478579 : Nat.Prime 7478579 := by norm_num
private theorem prime_t61_8109733 : Nat.Prime 8109733 := by norm_num
private theorem prime_t61_8295863 : Nat.Prime 8295863 := by norm_num
private theorem prime_t61_8724377 : Nat.Prime 8724377 := by norm_num
private theorem prime_t61_8943971 : Nat.Prime 8943971 := by norm_num
private theorem prime_t61_9238457 : Nat.Prime 9238457 := by norm_num
private theorem prime_t61_9743417 : Nat.Prime 9743417 := by norm_num
private theorem prime_t61_11461133 : Nat.Prime 11461133 := by norm_num
private theorem prime_t61_11633099 : Nat.Prime 11633099 := by norm_num
private theorem prime_t61_12040159 : Nat.Prime 12040159 := by norm_num
private theorem prime_t61_12712627 : Nat.Prime 12712627 := by norm_num
private theorem prime_t61_14584211 : Nat.Prime 14584211 := by norm_num
private theorem prime_t61_20930737 : Nat.Prime 20930737 := by norm_num
private theorem prime_t61_22795613 : Nat.Prime 22795613 := by norm_num
private theorem prime_t61_22977359 : Nat.Prime 22977359 := by norm_num
private theorem prime_t61_25210021 : Nat.Prime 25210021 := by norm_num
private theorem prime_t61_26200351 : Nat.Prime 26200351 := by norm_num
private theorem prime_t61_26854931 : Nat.Prime 26854931 := by norm_num
private theorem prime_t61_29343719 : Nat.Prime 29343719 := by norm_num

/-! ## Exact t=61 window totients -/

private theorem phi_t61_591133442051411133755680801 : Nat.totient 591133442051411133755680801 = 591133441567912245382206100 := by
  rw [← show ((([(1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680801 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680802 : Nat.totient 591133442051411133755680802 = 295566706904524787331297792 := by
  rw [← show ((([(2, 1), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680802 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680803 : Nat.totient 591133442051411133755680803 = 393116707140248427860776896 := by
  rw [← show ((([(3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680803 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_409, prime_t61_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680804 : Nat.totient 591133442051411133755680804 = 294019250239662992959575360 := by
  rw [← show ((([(2, 2), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680804 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680805 : Nat.totient 591133442051411133755680805 = 468224508555573175252024000 := by
  rw [← show ((([(5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680805 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680806 : Nat.totient 591133442051411133755680806 = 196410721061947504791863040 := by
  rw [← show ((([(2, 1), (3, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680806 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_311, prime_t61_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680807 : Nat.totient 591133442051411133755680807 = 504829729102411431936000000 := by
  rw [← show ((([(7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680807 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_433, prime_t61_751, prime_t61_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680808 : Nat.totient 591133442051411133755680808 = 295566721024224950550327168 := by
  rw [← show ((([(2, 3), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680808 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680809 : Nat.totient 591133442051411133755680809 = 393372004097683553918976000 := by
  rw [← show ((([(3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680809 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_1051, prime_t61_1153, prime_t61_940369, prime_t61_6947861, prime_t61_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680810 : Nat.totient 591133442051411133755680810 = 234727439763480041432912128 := by
  rw [← show ((([(2, 1), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680810 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_137, prime_lucas_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680811 : Nat.totient 591133442051411133755680811 = 537385815227551847710137600 := by
  rw [← show ((([(11, 1), (65353, 1), (10672982981, 1), (77044474757, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680811 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_11, prime_t61_65353, prime_lucas_10672982981, prime_lucas_77044474757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680812 : Nat.totient 591133442051411133755680812 = 195254997051989413824418560 := by
  rw [← show ((([(2, 2), (3, 1), (113, 1), (4271, 1), (102069566040058032487, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680812 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_113, prime_t61_4271, prime_lucas_102069566040058032487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680813 : Nat.totient 591133442051411133755680813 = 545661533072139799134615120 := by
  rw [← show ((([(13, 2), (5160187, 1), (677849662823399071, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680813 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_13, prime_t61_5160187, prime_lucas_677849662823399071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680814 : Nat.totient 591133442051411133755680814 = 250975093898704734640097568 := by
  rw [← show ((([(2, 1), (7, 1), (107, 1), (2106407, 1), (187340392836749749, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680814 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_t61_107, prime_t61_2106407, prime_lucas_187340392836749749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680815 : Nat.totient 591133442051411133755680815 = 315271142909118688380689952 := by
  rw [← show ((([(3, 1), (5, 1), (12040159, 1), (3273120906190752319, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680815 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_12040159, prime_lucas_3273120906190752319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680816 : Nat.totient 591133442051411133755680816 = 293185397670562357590240000 := by
  rw [← show ((([(2, 4), (139, 1), (1151, 1), (1214653051, 1), (190117973909, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680816 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_139, prime_t61_1151, prime_lucas_1214653051, prime_lucas_190117973909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680817 : Nat.totient 591133442051411133755680817 = 555245934677454242900955648 := by
  rw [← show ((([(17, 1), (499, 1), (1965292547, 1), (35457560705417, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680817 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_17, prime_t61_499, prime_lucas_1965292547, prime_lucas_35457560705417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680818 : Nat.totient 591133442051411133755680818 = 197044480683803711251893600 := by
  rw [← show ((([(2, 1), (3, 2), (32840746780633951875315601, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680818 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_lucas_32840746780633951875315601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680819 : Nat.totient 591133442051411133755680819 = 551662630915019828234849280 := by
  rw [← show ((([(19, 1), (67, 1), (442529322881, 1), (1049337207563, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680819 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_19, prime_t61_67, prime_lucas_442529322881, prime_lucas_1049337207563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680820 : Nat.totient 591133442051411133755680820 = 235681185625201858143716352 := by
  rw [← show ((([(2, 2), (5, 1), (307, 1), (120293, 1), (9238457, 1), (86631804463, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680820 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_307, prime_t61_120293, prime_t61_9238457, prime_lucas_86631804463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680821 : Nat.totient 591133442051411133755680821 = 337790531929316882839574976 := by
  rw [← show ((([(3, 1), (7, 1), (64596797, 1), (398497559, 1), (1093527187, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680821 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_7, prime_lucas_64596797, prime_lucas_398497559, prime_lucas_1093527187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680822 : Nat.totient 591133442051411133755680822 = 268696642867490884064625000 := by
  rw [← show ((([(2, 1), (11, 1), (714151, 1), (37624678690399899751, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680822 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_t61_714151, prime_lucas_37624678690399899751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680823 : Nat.totient 591133442051411133755680823 = 560244538617532051776422688 := by
  rw [← show ((([(23, 1), (109, 1), (235793155983809786101189, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680823 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_23, prime_t61_109, prime_lucas_235793155983809786101189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680824 : Nat.totient 591133442051411133755680824 = 197044480678460453112095456 := by
  rw [← show ((([(2, 3), (3, 1), (36879251603, 1), (667870388223167, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680824 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_lucas_36879251603, prime_lucas_667870388223167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680825 : Nat.totient 591133442051411133755680825 = 471745600609307262381587520 := by
  rw [← show ((([(5, 2), (467, 1), (5059, 1), (8543, 1), (1171530377614327, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680825 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_467, prime_t61_5059, prime_t61_8543, prime_lucas_1171530377614327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680826 : Nat.totient 591133442051411133755680826 = 271760886596082248902106496 := by
  rw [← show ((([(2, 1), (13, 1), (439, 1), (607, 1), (85321595874110948137, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680826 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_13, prime_t61_439, prime_t61_607, prime_lucas_85321595874110948137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680827 : Nat.totient 591133442051411133755680827 = 394064646578304014776854528 := by
  rw [← show ((([(3, 4), (16993, 1), (350737, 1), (1224472032347387, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680827 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_16993, prime_t61_350737, prime_lucas_1224472032347387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680828 : Nat.totient 591133442051411133755680828 = 253196997557963797363507200 := by
  rw [← show ((([(2, 2), (7, 1), (1801, 1), (48337, 1), (242512479730968673, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680828 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_t61_1801, prime_t61_48337, prime_lucas_242512479730968673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680829 : Nat.totient 591133442051411133755680829 = 570749180577339235363290112 := by
  rw [← show ((([(29, 1), (1632209, 1), (12488542701869825489, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680829 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_29, prime_t61_1632209, prime_lucas_12488542701869825489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680830 : Nat.totient 591133442051411133755680830 = 157389624883455182314721280 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (641, 1), (4107799, 1), (7483367271236279, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680830 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_t61_641, prime_t61_4107799, prime_lucas_7483367271236279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680831 : Nat.totient 591133442051411133755680831 = 571909862521123611303772800 := by
  rw [← show ((([(31, 1), (3697, 1), (26854931, 1), (192065934654443, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680831 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_31, prime_t61_3697, prime_t61_26854931, prime_lucas_192065934654443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680832 : Nat.totient 591133442051411133755680832 = 295506804804131331003594240 := by
  rw [← show ((([(2, 6), (4933, 1), (1872381924194871065261, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680832 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_4933, prime_lucas_1872381924194871065261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680833 : Nat.totient 591133442051411133755680833 = 355856313494523600720000000 := by
  rw [← show ((([(3, 1), (11, 1), (251, 1), (563, 1), (2027, 1), (2251, 1), (31397, 1), (884854933, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680833 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_11, prime_t61_251, prime_t61_563, prime_t61_2027, prime_t61_2251, prime_t61_31397, prime_lucas_884854933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680834 : Nat.totient 591133442051411133755680834 = 273975742046072796525379584 := by
  rw [← show ((([(2, 1), (17, 1), (83, 1), (617, 1), (673, 1), (504461807457102067, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680834 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_17, prime_t61_83, prime_t61_617, prime_t61_673, prime_lucas_504461807457102067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680835 : Nat.totient 591133442051411133755680835 = 400193965897803183515295744 := by
  rw [← show ((([(5, 1), (7, 1), (79, 1), (19759, 1), (116689, 1), (92724716540689, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680835 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_7, prime_t61_79, prime_t61_19759, prime_t61_116689, prime_lucas_92724716540689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680836 : Nat.totient 591133442051411133755680836 = 196958059922438514353332224 := by
  rw [← show ((([(2, 2), (3, 2), (2957, 1), (10709, 1), (272659, 1), (309667, 1), (6141409, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680836 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_2957, prime_t61_10709, prime_t61_272659, prime_t61_309667, prime_t61_6141409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680837 : Nat.totient 591133442051411133755680837 = 574901357052520003815590400 := by
  rw [← show ((([(37, 1), (2281, 1), (174749, 1), (8943971, 1), (4481397199, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680837 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_37, prime_t61_2281, prime_t61_174749, prime_t61_8943971, prime_lucas_4481397199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680838 : Nat.totient 591133442051411133755680838 = 278945898486162311407311360 := by
  rw [← show ((([(2, 1), (19, 1), (263, 1), (859443911, 1), (68822214862657, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680838 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_19, prime_t61_263, prime_lucas_859443911, prime_lucas_68822214862657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680839 : Nat.totient 591133442051411133755680839 = 363774425877791466926572800 := by
  rw [← show ((([(3, 1), (13, 1), (15157267744907977788607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680839 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_13, prime_lucas_15157267744907977788607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680840 : Nat.totient 591133442051411133755680840 = 236453376820564453502272320 := by
  rw [← show ((([(2, 3), (5, 1), (14778336051285278343892021, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680840 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_lucas_14778336051285278343892021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680841 : Nat.totient 591133442051411133755680841 = 576656819140432210528158720 := by
  rw [← show ((([(41, 2), (9829, 1), (9743417, 1), (3671953652077, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_41, prime_t61_9829, prime_t61_9743417, prime_lucas_3671953652077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680842 : Nat.totient 591133442051411133755680842 = 167761743861186668831907648 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (149, 1), (94460441363280781999949, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_7, prime_t61_149, prime_lucas_94460441363280781999949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680843 : Nat.totient 591133442051411133755680843 = 576712994242457575088441856 := by
  rw [← show ((([(43, 1), (859, 1), (622577, 1), (8109733, 1), (3169744679, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_43, prime_t61_859, prime_t61_622577, prime_t61_8109733, prime_lucas_3169744679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680844 : Nat.totient 591133442051411133755680844 = 268290303155312167303200000 := by
  rw [← show ((([(2, 2), (11, 1), (661, 1), (1276501, 1), (70401439, 1), (226166719, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_t61_661, prime_t61_1276501, prime_lucas_70401439, prime_lucas_226166719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680845 : Nat.totient 591133442051411133755680845 = 315094344506965452389292288 := by
  rw [← show ((([(3, 2), (5, 1), (1783, 1), (79467359, 1), (92711347287353, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_1783, prime_lucas_79467359, prime_lucas_92711347287353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680846 : Nat.totient 591133442051411133755680846 = 282715304461609968855467616 := by
  rw [← show ((([(2, 1), (23, 2), (409993, 1), (1362772683724253759, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_23, prime_t61_409993, prime_lucas_1362772683724253759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680847 : Nat.totient 591133442051411133755680847 = 578556134773385370961362232 := by
  rw [← show ((([(47, 1), (2774125132223, 1), (4533792341087, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_47, prime_lucas_2774125132223, prime_lucas_4533792341087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680848 : Nat.totient 591133442051411133755680848 = 197036542064058986876521600 := by
  rw [← show ((([(2, 4), (3, 1), (24821, 1), (496163734045273435931, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_24821, prime_lucas_496163734045273435931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680849 : Nat.totient 591133442051411133755680849 = 506683446829231255910970336 := by
  rw [← show ((([(7, 2), (315547, 1), (671189, 1), (56961388001447, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_315547, prime_t61_671189, prime_lucas_56961388001447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680850 : Nat.totient 591133442051411133755680850 = 236407490450552953336896000 := by
  rw [← show ((([(2, 1), (5, 2), (5503, 1), (95401, 1), (537037, 1), (41933284147, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_5503, prime_t61_95401, prime_t61_537037, prime_lucas_41933284147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680851 : Nat.totient 591133442051411133755680851 = 370677309054860531753629184 := by
  rw [← show ((([(3, 1), (17, 1), (1613, 1), (7185896965238456338277, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_17, prime_t61_1613, prime_lucas_7185896965238456338277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680852 : Nat.totient 591133442051411133755680852 = 270155142137787348356328960 := by
  rw [← show ((([(2, 2), (13, 1), (103, 1), (10069, 1), (206385271, 1), (53110442533, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_13, prime_t61_103, prime_t61_10069, prime_lucas_206385271, prime_lucas_53110442533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680853 : Nat.totient 591133442051411133755680853 = 579979961115582936934771408 := by
  rw [← show ((([(53, 1), (29343719, 1), (380097054868244279, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_53, prime_t61_29343719, prime_lucas_380097054868244279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680854 : Nat.totient 591133442051411133755680854 = 197010407592599272379570016 := by
  rw [← show ((([(2, 1), (3, 3), (5783, 1), (5630039669, 1), (336222770363, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5783, prime_lucas_5630039669, prime_lucas_336222770363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680855 : Nat.totient 591133442051411133755680855 = 429909980222811452294472480 := by
  rw [← show ((([(5, 1), (11, 1), (81883, 1), (131259000825215386867, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_11, prime_t61_81883, prime_lucas_131259000825215386867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680856 : Nat.totient 591133442051411133755680856 = 253342901907476051929891488 := by
  rw [← show ((([(2, 3), (7, 1), (138526327, 1), (76201791752889163, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680856 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_lucas_138526327, prime_lucas_76201791752889163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680857 : Nat.totient 591133442051411133755680857 = 370491976013769746885548800 := by
  rw [← show ((([(3, 1), (19, 1), (131, 1), (77477, 1), (530333, 1), (1926717003131, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680857 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_19, prime_t61_131, prime_t61_77477, prime_t61_530333, prime_lucas_1926717003131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680858 : Nat.totient 591133442051411133755680858 = 284784776937164799839900160 := by
  rw [← show ((([(2, 1), (29, 1), (487, 1), (71143, 1), (294168658296142561, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680858 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_29, prime_t61_487, prime_t61_71143, prime_lucas_294168658296142561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680859 : Nat.totient 591133442051411133755680859 = 580933592614266454993568256 := by
  rw [← show ((([(59, 1), (3217, 1), (3114457843402955347153, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680859 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_59, prime_t61_3217, prime_lucas_3114457843402955347153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680860 : Nat.totient 591133442051411133755680860 = 157635520209060518718929152 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (2450117, 1), (4021123903140211493, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680860 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_t61_2450117, prime_lucas_4021123903140211493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680861 : Nat.totient 591133442051411133755680861 = 579009915117233760205152240 := by
  rw [← show ((([(61, 1), (239, 1), (40546912823335697493359, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680861 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_61, prime_t61_239, prime_lucas_40546912823335697493359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680862 : Nat.totient 591133442051411133755680862 = 286032310670037645365652000 := by
  rw [← show ((([(2, 1), (31, 1), (9534410355667921512188401, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680862 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_31, prime_lucas_9534410355667921512188401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680863 : Nat.totient 591133442051411133755680863 = 335127021913026411133379328 := by
  rw [← show ((([(3, 2), (7, 1), (127, 1), (89759, 1), (22795613, 1), (36108710389, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680863 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_7, prime_t61_127, prime_t61_89759, prime_t61_22795613, prime_lucas_36108710389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680864 : Nat.totient 591133442051411133755680864 = 295566721025705566877840416 := by
  rw [← show ((([(2, 5), (18472920064106597929865027, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680864 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_lucas_18472920064106597929865027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680865 : Nat.totient 591133442051411133755680865 = 430381010897668777772280000 := by
  rw [← show ((([(5, 1), (13, 1), (71, 1), (128089586576687136241751, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680865 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_13, prime_t61_71, prime_lucas_128089586576687136241751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680866 : Nat.totient 591133442051411133755680866 = 176428327529709699918566400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (73, 1), (743, 1), (15511, 1), (10646089723492169, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680866 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_11, prime_t61_73, prime_t61_743, prime_t61_15511, prime_lucas_10646089723492169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680867 : Nat.totient 591133442051411133755680867 = 591130107054458642276159232 := by
  rw [← show ((([(188843, 1), (2887697, 1), (1084009320845977, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680867 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_188843, prime_t61_2887697, prime_lucas_1084009320845977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680868 : Nat.totient 591133442051411133755680868 = 277758318214641453903944832 := by
  rw [← show ((([(2, 2), (17, 2), (659, 1), (775965264098654160067, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680868 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_17, prime_t61_659, prime_lucas_775965264098654160067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680869 : Nat.totient 591133442051411133755680869 = 376954658699450578047100800 := by
  rw [← show ((([(3, 1), (23, 1), (8567151334078422228343201, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680869 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_23, prime_lucas_8567151334078422228343201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680870 : Nat.totient 591133442051411133755680870 = 200584895054703942178685952 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (97, 1), (104245727, 1), (835136552805839, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680870 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_7, prime_t61_97, prime_lucas_104245727, prime_lucas_835136552805839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680871 : Nat.totient 591133442051411133755680871 = 591101950110201346803866880 := by
  rw [← show ((([(34613, 1), (41641, 1), (2711039, 1), (151282736333, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680871 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_34613, prime_t61_41641, prime_t61_2711039, prime_lucas_151282736333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680872 : Nat.totient 591133442051411133755680872 = 196958322187658628737080608 := by
  rw [← show ((([(2, 3), (3, 2), (2287, 1), (3589937339378438114923, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680872 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_2287, prime_lucas_3589937339378438114923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680873 : Nat.totient 591133442051411133755680873 = 591100209917574432630374400 := by
  rw [← show ((([(17921, 1), (2396833, 1), (13762125499650761, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680873 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_17921, prime_t61_2396833, prime_lucas_13762125499650761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680874 : Nat.totient 591133442051411133755680874 = 287398357109664050001350592 := by
  rw [← show ((([(2, 1), (37, 1), (1597, 1), (5002059960833751914533, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680874 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_37, prime_t61_1597, prime_lucas_5002059960833751914533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680875 : Nat.totient 591133442051411133755680875 = 315116891013348428814656000 := by
  rw [← show ((([(3, 1), (5, 3), (2063, 1), (216371, 1), (3531473741088113, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680875 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_2063, prime_t61_216371, prime_lucas_3531473741088113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680876 : Nat.totient 591133442051411133755680876 = 279997398984918065272601184 := by
  rw [← show ((([(2, 2), (19, 2), (21247, 1), (19267293725528112157, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680876 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_19, prime_t61_21247, prime_lucas_19267293725528112157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680877 : Nat.totient 591133442051411133755680877 = 460623429755053836795942000 := by
  rw [← show ((([(7, 1), (11, 3), (14584211, 1), (4350372999962771, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680877 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_11, prime_t61_14584211, prime_lucas_4350372999962771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680878 : Nat.totient 591133442051411133755680878 = 181887212913899094589075296 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (7276517639, 1), (1041519343241159, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680878 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_13, prime_lucas_7276517639, prime_lucas_1041519343241159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680879 : Nat.totient 591133442051411133755680879 = 590498000406573291831052800 := by
  rw [← show ((([(1399, 1), (2801, 1), (293957, 1), (513181390850053, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680879 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_1399, prime_t61_2801, prime_t61_293957, prime_lucas_513181390850053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680880 : Nat.totient 591133442051411133755680880 = 236453358220681295934918144 := by
  rw [← show ((([(2, 4), (5, 1), (12712627, 1), (581246348661267193, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680880 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_12712627, prime_lucas_581246348661267193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680881 : Nat.totient 591133442051411133755680881 = 394081692633421325754143904 := by
  rw [← show ((([(3, 3), (54217, 1), (403818565894263814859, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680881 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_54217, prime_lucas_403818565894263814859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680882 : Nat.totient 591133442051411133755680882 = 288357467746247196387634080 := by
  rw [← show ((([(2, 1), (41, 1), (933607, 1), (7721604931476639943, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680882 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_41, prime_t61_933607, prime_lucas_7721604931476639943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680883 : Nat.totient 591133442051411133755680883 = 577899725340971122467840000 := by
  rw [← show ((([(89, 1), (173, 1), (181, 1), (222461, 1), (26200351, 1), (36392329, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680883 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_89, prime_t61_173, prime_t61_181, prime_t61_222461, prime_t61_26200351, prime_lucas_36392329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680884 : Nat.totient 591133442051411133755680884 = 168895269157546038215908800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (7037302881564418258996201, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680884 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_7, prime_lucas_7037302881564418258996201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680885 : Nat.totient 591133442051411133755680885 = 443806013598665336195822592 := by
  rw [← show ((([(5, 1), (17, 1), (347, 1), (22977359, 1), (872242048482397, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680885 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_17, prime_t61_347, prime_t61_22977359, prime_lucas_872242048482397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680886 : Nat.totient 591133442051411133755680886 = 283592043106180268675269824 := by
  rw [← show ((([(2, 1), (43, 1), (67, 2), (359, 1), (11461133, 1), (372147813547, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680886 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_43, prime_t61_67, prime_t61_359, prime_t61_11461133, prime_lucas_372147813547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680887 : Nat.totient 591133442051411133755680887 = 380498248929146441084479488 := by
  rw [← show ((([(3, 1), (29, 1), (418709, 1), (719057, 1), (22567874715277, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680887 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_29, prime_t61_418709, prime_t61_719057, prime_lucas_22567874715277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680888 : Nat.totient 591133442051411133755680888 = 268697018006864596393272160 := by
  rw [← show ((([(2, 3), (11, 1), (242634839, 1), (27685329549302459, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680888 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_lucas_242634839, prime_lucas_27685329549302459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680889 : Nat.totient 591133442051411133755680889 = 591133282346778542662909056 := by
  rw [← show ((([(3701417, 1), (159704632591089070417, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680889 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3701417, prime_lucas_159704632591089070417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680890 : Nat.totient 591133442051411133755680890 = 157635584546905160279059968 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1576960157497, 1), (4165069944793, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680890 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_lucas_1576960157497, prime_lucas_4165069944793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680891 : Nat.totient 591133442051411133755680891 = 467342191757105661745157760 := by
  rw [← show ((([(7, 1), (13, 1), (1327, 1), (30491, 1), (160546760241452093, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680891 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_13, prime_t61_1327, prime_t61_30491, prime_lucas_160546760241452093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680892 : Nat.totient 591133442051411133755680892 = 280489306882121308146859200 := by
  rw [← show ((([(2, 2), (23, 1), (199, 1), (349, 1), (92516500850366685451, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680892 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_23, prime_t61_199, prime_t61_349, prime_lucas_92516500850366685451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680893 : Nat.totient 591133442051411133755680893 = 379969121185289861002326000 := by
  rw [← show ((([(3, 1), (31, 1), (271, 1), (23454884023783324753231, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680893 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_31, prime_t61_271, prime_lucas_23454884023783324753231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_591133442051411133755680894 : Nat.totient 591133442051411133755680894 = 288028960232923964141936640 := by
  rw [← show ((([(2, 1), (47, 1), (257, 1), (2333, 1), (10488413807049922021, 1)] : List FactorBlock).map factorBlockValue).prod) = 591133442051411133755680894 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_47, prime_t61_257, prime_t61_2333, prime_lucas_10488413807049922021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361601 : Nat.totient 1182266884102822267511361601 = 1170554827853295639500976192 := by
  rw [← show ((([(103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_103, prime_t61_5009, prime_lucas_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361602 : Nat.totient 1182266884102822267511361602 = 591133441567912245382206100 := by
  rw [← show ((([(2, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_lucas_1222615931, prime_lucas_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361603 : Nat.totient 1182266884102822267511361603 = 788177922735214845007574400 := by
  rw [← show ((([(3, 1), (394088961367607422503787201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_lucas_394088961367607422503787201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361604 : Nat.totient 1182266884102822267511361604 = 591133413809049574662595584 := by
  rw [← show ((([(2, 2), (20930737, 1), (14121180779525611873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_20930737, prime_lucas_14121180779525611873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361605 : Nat.totient 1182266884102822267511361605 = 945813505771568331823918608 := by
  rw [← show ((([(5, 1), (626080687, 1), (377672369920211983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_lucas_626080687, prime_lucas_377672369920211983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361606 : Nat.totient 1182266884102822267511361606 = 393116707140248427860776896 := by
  rw [← show ((([(2, 1), (3, 1), (409, 1), (45127, 1), (10675900157669865007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_409, prime_t61_45127, prime_lucas_10675900157669865007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361607 : Nat.totient 1182266884102822267511361607 = 1011173411801001135106919520 := by
  rw [← show ((([(7, 1), (461, 1), (13492702567, 1), (27152987060723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_461, prime_lucas_13492702567, prime_lucas_27152987060723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361608 : Nat.totient 1182266884102822267511361608 = 588038500479325985919150720 := by
  rw [← show ((([(2, 3), (191, 1), (282045737, 1), (2743295750628703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_191, prime_lucas_282045737, prime_lucas_2743295750628703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361609 : Nat.totient 1182266884102822267511361609 = 788177922735214845007574400 := by
  rw [← show ((([(3, 2), (131362987122535807501262401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_lucas_131362987122535807501262401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361610 : Nat.totient 1182266884102822267511361610 = 468224508555573175252024000 := by
  rw [← show ((([(2, 1), (5, 1), (101, 1), (1170561271388932938130061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_101, prime_lucas_1170561271388932938130061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361611 : Nat.totient 1182266884102822267511361611 = 1074788076457111152283056000 := by
  rw [← show ((([(11, 1), (107478807645711115228305601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_11, prime_lucas_107478807645711115228305601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361612 : Nat.totient 1182266884102822267511361612 = 392821442123895009583726080 := by
  rw [← show ((([(2, 2), (3, 1), (311, 1), (1115447, 1), (284004322561366753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_311, prime_t61_1115447, prime_lucas_284004322561366753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361613 : Nat.totient 1182266884102822267511361613 = 1091322450430260586490332224 := by
  rw [← show ((([(13, 1), (1319293, 1), (68933592817856129557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_13, prime_t61_1319293, prime_lucas_68933592817856129557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361614 : Nat.totient 1182266884102822267511361614 = 504829729102411431936000000 := by
  rw [← show ((([(2, 1), (7, 1), (433, 1), (751, 1), (39551, 1), (40376737, 1), (162618881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_t61_433, prime_t61_751, prime_t61_39551, prime_lucas_40376737, prime_lucas_162618881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361615 : Nat.totient 1182266884102822267511361615 = 630542218085853059114011296 := by
  rw [← show ((([(3, 1), (5, 1), (5250043, 1), (15012789852106255987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_5250043, prime_lucas_15012789852106255987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361616 : Nat.totient 1182266884102822267511361616 = 591133442048449901100654336 := by
  rw [← show ((([(2, 4), (199731886537, 1), (369954349991773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_lucas_199731886537, prime_lucas_369954349991773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361617 : Nat.totient 1182266884102822267511361617 = 1112721773273244487069516800 := by
  rw [← show ((([(17, 1), (69545110829577780441844801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_17, prime_lucas_69545110829577780441844801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361618 : Nat.totient 1182266884102822267511361618 = 393372004097683553918976000 := by
  rw [← show ((([(2, 1), (3, 2), (1051, 1), (1153, 1), (940369, 1), (6947861, 1), (8295863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_1051, prime_t61_1153, prime_t61_940369, prime_t61_6947861, prime_t61_8295863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361619 : Nat.totient 1182266884102822267511361619 = 1118619131698437065522004456 := by
  rw [← show ((([(19, 1), (787, 1), (79065530937124474520923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_19, prime_t61_787, prime_lucas_79065530937124474520923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361620 : Nat.totient 1182266884102822267511361620 = 469454879526960082865824256 := by
  rw [← show ((([(2, 2), (5, 1), (137, 1), (431484264271103017339913, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_137, prime_lucas_431484264271103017339913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361621 : Nat.totient 1182266884102822267511361621 = 674536901859503806414070064 := by
  rw [← show ((([(3, 1), (7, 1), (647, 1), (87014564223362204129783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_7, prime_t61_647, prime_lucas_87014564223362204129783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361622 : Nat.totient 1182266884102822267511361622 = 537385815227551847710137600 := by
  rw [← show ((([(2, 1), (11, 1), (65353, 1), (10672982981, 1), (77044474757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_t61_65353, prime_lucas_10672982981, prime_lucas_77044474757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361623 : Nat.totient 1182266884102822267511361623 = 1130720846877228034389940000 := by
  rw [← show ((([(23, 1), (7901, 1), (6505873687440897781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_23, prime_t61_7901, prime_lucas_6505873687440897781301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361624 : Nat.totient 1182266884102822267511361624 = 390509994103978827648837120 := by
  rw [← show ((([(2, 3), (3, 1), (113, 1), (4271, 1), (102069566040058032487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_113, prime_t61_4271, prime_lucas_102069566040058032487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361625 : Nat.totient 1182266884102822267511361625 = 945807159723492911330304000 := by
  rw [← show ((([(5, 3), (149059, 1), (407047681, 1), (155884173167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_149059, prime_lucas_407047681, prime_lucas_155884173167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361626 : Nat.totient 1182266884102822267511361626 = 545661533072139799134615120 := by
  rw [← show ((([(2, 1), (13, 2), (5160187, 1), (677849662823399071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_13, prime_t61_5160187, prime_lucas_677849662823399071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361627 : Nat.totient 1182266884102822267511361627 = 788177922734890937629881576 := by
  rw [← show ((([(3, 3), (2901032068267, 1), (15093822248003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_lucas_2901032068267, prime_lucas_15093822248003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361628 : Nat.totient 1182266884102822267511361628 = 501950187797409469280195136 := by
  rw [← show ((([(2, 2), (7, 1), (107, 1), (2106407, 1), (187340392836749749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_t61_107, prime_t61_2106407, prime_lucas_187340392836749749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361629 : Nat.totient 1182266884102822267511361629 = 1141213757073801325196800000 := by
  rw [← show ((([(29, 1), (4001, 1), (10189408545301797546401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_29, prime_t61_4001, prime_lucas_10189408545301797546401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361630 : Nat.totient 1182266884102822267511361630 = 315271142909118688380689952 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (12040159, 1), (3273120906190752319, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_t61_12040159, prime_lucas_3273120906190752319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361631 : Nat.totient 1182266884102822267511361631 = 1143324662113825832429601120 := by
  rw [← show ((([(31, 1), (1423, 1), (3748763, 1), (4597727, 1), (1554954787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_31, prime_t61_1423, prime_t61_3748763, prime_t61_4597727, prime_lucas_1554954787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361632 : Nat.totient 1182266884102822267511361632 = 586370795341124715180480000 := by
  rw [← show ((([(2, 5), (139, 1), (1151, 1), (1214653051, 1), (190117973909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_139, prime_t61_1151, prime_lucas_1214653051, prime_lucas_190117973909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361633 : Nat.totient 1182266884102822267511361633 = 716525294224298420086473600 := by
  rw [← show ((([(3, 1), (11, 2), (11633099, 1), (25210021, 1), (11105555029, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_11, prime_t61_11633099, prime_t61_25210021, prime_lucas_11105555029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361634 : Nat.totient 1182266884102822267511361634 = 555245934677454242900955648 := by
  rw [← show ((([(2, 1), (17, 1), (499, 1), (1965292547, 1), (35457560705417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_17, prime_t61_499, prime_lucas_1965292547, prime_lucas_35457560705417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361635 : Nat.totient 1182266884102822267511361635 = 807189700743848057422556160 := by
  rw [← show ((([(5, 1), (7, 1), (233, 1), (28621, 1), (5065318471177066877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_7, prime_t61_233, prime_t61_28621, prime_lucas_5065318471177066877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361636 : Nat.totient 1182266884102822267511361636 = 394088961367607422503787200 := by
  rw [← show ((([(2, 2), (3, 2), (32840746780633951875315601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_lucas_32840746780633951875315601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361637 : Nat.totient 1182266884102822267511361637 = 1146690578612362057176672000 := by
  rw [← show ((([(37, 1), (431, 1), (1973, 1), (3187, 1), (90931, 1), (129662805691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_37, prime_t61_431, prime_t61_1973, prime_t61_3187, prime_t61_90931, prime_lucas_129662805691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361638 : Nat.totient 1182266884102822267511361638 = 551662630915019828234849280 := by
  rw [← show ((([(2, 1), (19, 1), (67, 1), (442529322881, 1), (1049337207563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_19, prime_t61_67, prime_lucas_442529322881, prime_lucas_1049337207563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361639 : Nat.totient 1182266884102822267511361639 = 727531201799207407228982400 := by
  rw [← show ((([(3, 1), (13, 1), (41221, 1), (735414848980275965581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_13, prime_t61_41221, prime_lucas_735414848980275965581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361640 : Nat.totient 1182266884102822267511361640 = 471362371250403716287432704 := by
  rw [← show ((([(2, 3), (5, 1), (307, 1), (120293, 1), (9238457, 1), (86631804463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_307, prime_t61_120293, prime_t61_9238457, prime_lucas_86631804463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361641 : Nat.totient 1182266884102822267511361641 = 1146211887247010197130649600 := by
  rw [← show ((([(41, 1), (167, 1), (3769, 1), (138977, 1), (329644722325231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_41, prime_t61_167, prime_t61_3769, prime_t61_138977, prime_lucas_329644722325231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361642 : Nat.totient 1182266884102822267511361642 = 337790531929316882839574976 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (64596797, 1), (398497559, 1), (1093527187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_7, prime_lucas_64596797, prime_lucas_398497559, prime_lucas_1093527187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361643 : Nat.totient 1182266884102822267511361643 = 1142867436261497695543447296 := by
  rw [← show ((([(43, 1), (97, 1), (87628772527, 1), (3234659767279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_43, prime_t61_97, prime_lucas_87628772527, prime_lucas_3234659767279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361644 : Nat.totient 1182266884102822267511361644 = 537393285734981768129250000 := by
  rw [← show ((([(2, 2), (11, 1), (714151, 1), (37624678690399899751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_t61_714151, prime_lucas_37624678690399899751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361645 : Nat.totient 1182266884102822267511361645 = 627605493218555954201814528 := by
  rw [← show ((([(3, 2), (5, 1), (223, 1), (5743, 1), (20514424207990512529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_223, prime_t61_5743, prime_lucas_20514424207990512529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361646 : Nat.totient 1182266884102822267511361646 = 560244538617532051776422688 := by
  rw [← show ((([(2, 1), (23, 1), (109, 1), (235793155983809786101189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_23, prime_t61_109, prime_lucas_235793155983809786101189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361647 : Nat.totient 1182266884102822267511361647 = 1157112269547443070330268800 := by
  rw [← show ((([(47, 1), (25154614555379197181092801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_47, prime_lucas_25154614555379197181092801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361648 : Nat.totient 1182266884102822267511361648 = 394088961356920906224190912 := by
  rw [← show ((([(2, 4), (3, 1), (36879251603, 1), (667870388223167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_lucas_36879251603, prime_lucas_667870388223167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361649 : Nat.totient 1182266884102822267511361649 = 1013239991148036941565645768 := by
  rw [← show ((([(7, 2), (7699, 1), (3133899934268755463899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_7699, prime_lucas_3133899934268755463899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361650 : Nat.totient 1182266884102822267511361650 = 471745600609307262381587520 := by
  rw [← show ((([(2, 1), (5, 2), (467, 1), (5059, 1), (8543, 1), (1171530377614327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_467, prime_t61_5059, prime_t61_8543, prime_lucas_1171530377614327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361651 : Nat.totient 1182266884102822267511361651 = 740215110912404325369924096 := by
  rw [← show ((([(3, 1), (17, 1), (1103, 1), (1579, 1), (1619, 1), (8221306843187167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_17, prime_t61_1103, prime_t61_1579, prime_t61_1619, prime_lucas_8221306843187167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361652 : Nat.totient 1182266884102822267511361652 = 543521773192164497804212992 := by
  rw [← show ((([(2, 2), (13, 1), (439, 1), (607, 1), (85321595874110948137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_13, prime_t61_439, prime_t61_607, prime_lucas_85321595874110948137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361653 : Nat.totient 1182266884102822267511361653 = 1156931345673110080390427344 := by
  rw [← show ((([(53, 1), (383, 1), (58242617079798131312447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_53, prime_t61_383, prime_lucas_58242617079798131312447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361654 : Nat.totient 1182266884102822267511361654 = 394064646578304014776854528 := by
  rw [← show ((([(2, 1), (3, 4), (16993, 1), (350737, 1), (1224472032347387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_16993, prime_t61_350737, prime_lucas_1224472032347387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361655 : Nat.totient 1182266884102822267511361655 = 859830461145444416251161760 := by
  rw [← show ((([(5, 1), (11, 1), (42475852319, 1), (506070163529759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_11, prime_lucas_42475852319, prime_lucas_506070163529759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361656 : Nat.totient 1182266884102822267511361656 = 506393995115927594727014400 := by
  rw [← show ((([(2, 3), (7, 1), (1801, 1), (48337, 1), (242512479730968673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_7, prime_t61_1801, prime_t61_48337, prime_lucas_242512479730968673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361657 : Nat.totient 1182266884102822267511361657 = 746694874096460483706129600 := by
  rw [← show ((([(3, 1), (19, 1), (10125680021, 1), (2048408031805181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_19, prime_lucas_10125680021, prime_lucas_2048408031805181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361658 : Nat.totient 1182266884102822267511361658 = 570749180577339235363290112 := by
  rw [← show ((([(2, 1), (29, 1), (1632209, 1), (12488542701869825489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_29, prime_t61_1632209, prime_lucas_12488542701869825489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361659 : Nat.totient 1182266884102822267511361659 = 1116690320675732589273876480 := by
  rw [← show ((([(59, 1), (71, 1), (73, 1), (157, 1), (179, 1), (137571863802922249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_59, prime_t61_71, prime_t61_73, prime_t61_157, prime_t61_179, prime_lucas_137571863802922249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361660 : Nat.totient 1182266884102822267511361660 = 314779249766910364629442560 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (641, 1), (4107799, 1), (7483367271236279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_t61_641, prime_t61_4107799, prime_lucas_7483367271236279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361661 : Nat.totient 1182266884102822267511361661 = 1162885459773267804109536000 := by
  rw [← show ((([(61, 1), (19381424329554463401825601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_61, prime_lucas_19381424329554463401825601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361662 : Nat.totient 1182266884102822267511361662 = 571909862521123611303772800 := by
  rw [← show ((([(2, 1), (31, 1), (3697, 1), (26854931, 1), (192065934654443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_31, prime_t61_3697, prime_t61_26854931, prime_lucas_192065934654443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361663 : Nat.totient 1182266884102822267511361663 = 675569474887527660887283600 := by
  rw [← show ((([(3, 2), (7, 1), (58231, 1), (322270629346999284871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_7, prime_t61_58231, prime_lucas_322270629346999284871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361664 : Nat.totient 1182266884102822267511361664 = 591013609608262662007188480 := by
  rw [← show ((([(2, 7), (4933, 1), (1872381924194871065261, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_4933, prime_lucas_1872381924194871065261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361665 : Nat.totient 1182266884102822267511361665 = 872570607225700806526079232 := by
  rw [← show ((([(5, 1), (13, 1), (1789, 1), (10166976687473210366869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_13, prime_t61_1789, prime_lucas_10166976687473210366869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361666 : Nat.totient 1182266884102822267511361666 = 355856313494523600720000000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (251, 1), (563, 1), (2027, 1), (2251, 1), (31397, 1), (884854933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_11, prime_t61_251, prime_t61_563, prime_t61_2027, prime_t61_2251, prime_t61_31397, prime_lucas_884854933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361667 : Nat.totient 1182266884102822267511361667 = 1180488778993030262497327872 := by
  rw [← show ((([(683, 1), (31337, 1), (125029, 1), (441800950636813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_683, prime_t61_31337, prime_t61_125029, prime_lucas_441800950636813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361668 : Nat.totient 1182266884102822267511361668 = 547951484092145593050759168 := by
  rw [← show ((([(2, 2), (17, 1), (83, 1), (617, 1), (673, 1), (504461807457102067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_17, prime_t61_83, prime_t61_617, prime_t61_673, prime_lucas_504461807457102067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361669 : Nat.totient 1182266884102822267511361669 = 753901306546637351634087600 := by
  rw [← show ((([(3, 1), (23, 1), (94111, 1), (182064824177373999391, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_23, prime_t61_94111, prime_lucas_182064824177373999391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361670 : Nat.totient 1182266884102822267511361670 = 400193965897803183515295744 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (79, 1), (19759, 1), (116689, 1), (92724716540689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_t61_7, prime_t61_79, prime_t61_19759, prime_t61_116689, prime_lucas_92724716540689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361671 : Nat.totient 1182266884102822267511361671 = 1175430706123956741727285248 := by
  rw [← show ((([(197, 1), (1409, 1), (4036298429, 1), (1055249212663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_197, prime_t61_1409, prime_lucas_4036298429, prime_lucas_1055249212663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361672 : Nat.totient 1182266884102822267511361672 = 393916119844877028706664448 := by
  rw [← show ((([(2, 3), (3, 2), (2957, 1), (10709, 1), (272659, 1), (309667, 1), (6141409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_2957, prime_t61_10709, prime_t61_272659, prime_t61_309667, prime_t61_6141409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361673 : Nat.totient 1182266884102822267511361673 = 1181901862876059772829464320 := by
  rw [← show ((([(3739, 1), (44959, 1), (52453, 1), (134082804329041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3739, prime_t61_44959, prime_t61_52453, prime_lucas_134082804329041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361674 : Nat.totient 1182266884102822267511361674 = 574901357052520003815590400 := by
  rw [← show ((([(2, 1), (37, 1), (2281, 1), (174749, 1), (8943971, 1), (4481397199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_37, prime_t61_2281, prime_t61_174749, prime_t61_8943971, prime_lucas_4481397199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361675 : Nat.totient 1182266884102822267511361675 = 630541255977730511078556960 := by
  rw [← show ((([(3, 1), (5, 2), (582643, 1), (27055261034122604923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_5, prime_t61_582643, prime_lucas_27055261034122604923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361676 : Nat.totient 1182266884102822267511361676 = 557891796972324622814622720 := by
  rw [← show ((([(2, 2), (19, 1), (263, 1), (859443911, 1), (68822214862657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_19, prime_t61_263, prime_lucas_859443911, prime_lucas_68822214862657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361677 : Nat.totient 1182266884102822267511361677 = 907883012113761636281472000 := by
  rw [← show ((([(7, 1), (11, 1), (89, 1), (521, 1), (719, 1), (460540872544088591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_11, prime_t61_89, prime_t61_521, prime_t61_719, prime_lucas_460540872544088591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361678 : Nat.totient 1182266884102822267511361678 = 363774425877791466926572800 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (15157267744907977788607201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_13, prime_lucas_15157267744907977788607201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361679 : Nat.totient 1182266884102822267511361679 = 1182251467550236957608105216 := by
  rw [← show ((([(76697, 1), (664551479, 1), (23195755332433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_76697, prime_lucas_664551479, prime_lucas_23195755332433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361680 : Nat.totient 1182266884102822267511361680 = 472906753641128907004544640 := by
  rw [← show ((([(2, 4), (5, 1), (14778336051285278343892021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_5, prime_lucas_14778336051285278343892021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361681 : Nat.totient 1182266884102822267511361681 = 788177910387450727738576080 := by
  rw [← show ((([(3, 3), (63831631, 1), (685986895340001613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_lucas_63831631, prime_lucas_685986895340001613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361682 : Nat.totient 1182266884102822267511361682 = 576656819140432210528158720 := by
  rw [← show ((([(2, 1), (41, 2), (9829, 1), (9743417, 1), (3671953652077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_41, prime_t61_9829, prime_t61_9743417, prime_lucas_3671953652077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361683 : Nat.totient 1182266884102822267511361683 = 1182266879779521307096941000 := by
  rw [← show ((([(273463933, 1), (4323300960140956751, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_lucas_273463933, prime_lucas_4323300960140956751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361684 : Nat.totient 1182266884102822267511361684 = 335523487722373337663815296 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (149, 1), (94460441363280781999949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_7, prime_t61_149, prime_lucas_94460441363280781999949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361685 : Nat.totient 1182266884102822267511361685 = 890176686902373699680256000 := by
  rw [← show ((([(5, 1), (17, 1), (1216561, 1), (11433065967029648401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_5, prime_t61_17, prime_t61_1216561, prime_lucas_11433065967029648401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361686 : Nat.totient 1182266884102822267511361686 = 576712994242457575088441856 := by
  rw [← show ((([(2, 1), (43, 1), (859, 1), (622577, 1), (8109733, 1), (3169744679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_43, prime_t61_859, prime_t61_622577, prime_t61_8109733, prime_lucas_3169744679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361687 : Nat.totient 1182266884102822267511361687 = 760999373674466774804208224 := by
  rw [← show ((([(3, 1), (29, 1), (881055049019, 1), (15423865449779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_29, prime_lucas_881055049019, prime_lucas_15423865449779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361688 : Nat.totient 1182266884102822267511361688 = 536580606310624334606400000 := by
  rw [← show ((([(2, 3), (11, 1), (661, 1), (1276501, 1), (70401439, 1), (226166719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_11, prime_t61_661, prime_t61_1276501, prime_lucas_70401439, prime_lucas_226166719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361689 : Nat.totient 1182266884102822267511361689 = 1182233813869473880568958720 := by
  rw [← show ((([(36073, 1), (7478579, 1), (8724377, 1), (502319171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_36073, prime_t61_7478579, prime_t61_8724377, prime_lucas_502319171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361690 : Nat.totient 1182266884102822267511361690 = 315094344506965452389292288 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1783, 1), (79467359, 1), (92711347287353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_3, prime_t61_5, prime_t61_1783, prime_lucas_79467359, prime_lucas_92711347287353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361691 : Nat.totient 1182266884102822267511361691 = 935419952257178057811187200 := by
  rw [← show ((([(7, 1), (13, 1), (12991943781349695247377601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_7, prime_t61_13, prime_lucas_12991943781349695247377601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361692 : Nat.totient 1182266884102822267511361692 = 565430608923219937710935232 := by
  rw [← show ((([(2, 2), (23, 2), (409993, 1), (1362772683724253759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_23, prime_t61_409993, prime_lucas_1362772683724253759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361693 : Nat.totient 1182266884102822267511361693 = 762671895021725960773370880 := by
  rw [← show ((([(3, 1), (31, 2), (12497, 1), (38329, 1), (856125876868967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_3, prime_t61_31, prime_t61_12497, prime_t61_38329, prime_lucas_856125876868967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_t61_1182266884102822267511361694 : Nat.totient 1182266884102822267511361694 = 578556134773385370961362232 := by
  rw [← show ((([(2, 1), (47, 1), (2774125132223, 1), (4533792341087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822267511361694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_t61_2, prime_t61_47, prime_lucas_2774125132223, prime_lucas_4533792341087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The twenty-seventh finite diagonal certificate -/

theorem certifiedKill_diagonal_t61 :
    certifiedKill (periodLcm 61) (periodLcm 61) 94 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_t61_591133442051411133755680801, phi_t61_591133442051411133755680802, phi_t61_591133442051411133755680803, phi_t61_591133442051411133755680804, phi_t61_591133442051411133755680805, phi_t61_591133442051411133755680806, phi_t61_591133442051411133755680807, phi_t61_591133442051411133755680808, phi_t61_591133442051411133755680809, phi_t61_591133442051411133755680810, phi_t61_591133442051411133755680811, phi_t61_591133442051411133755680812, phi_t61_591133442051411133755680813, phi_t61_591133442051411133755680814, phi_t61_591133442051411133755680815, phi_t61_591133442051411133755680816, phi_t61_591133442051411133755680817, phi_t61_591133442051411133755680818, phi_t61_591133442051411133755680819, phi_t61_591133442051411133755680820, phi_t61_591133442051411133755680821, phi_t61_591133442051411133755680822, phi_t61_591133442051411133755680823, phi_t61_591133442051411133755680824, phi_t61_591133442051411133755680825, phi_t61_591133442051411133755680826, phi_t61_591133442051411133755680827, phi_t61_591133442051411133755680828, phi_t61_591133442051411133755680829, phi_t61_591133442051411133755680830, phi_t61_591133442051411133755680831, phi_t61_591133442051411133755680832, phi_t61_591133442051411133755680833, phi_t61_591133442051411133755680834, phi_t61_591133442051411133755680835, phi_t61_591133442051411133755680836, phi_t61_591133442051411133755680837, phi_t61_591133442051411133755680838, phi_t61_591133442051411133755680839, phi_t61_591133442051411133755680840, phi_t61_591133442051411133755680841, phi_t61_591133442051411133755680842, phi_t61_591133442051411133755680843, phi_t61_591133442051411133755680844, phi_t61_591133442051411133755680845, phi_t61_591133442051411133755680846, phi_t61_591133442051411133755680847, phi_t61_591133442051411133755680848, phi_t61_591133442051411133755680849, phi_t61_591133442051411133755680850, phi_t61_591133442051411133755680851, phi_t61_591133442051411133755680852, phi_t61_591133442051411133755680853, phi_t61_591133442051411133755680854, phi_t61_591133442051411133755680855, phi_t61_591133442051411133755680856, phi_t61_591133442051411133755680857, phi_t61_591133442051411133755680858, phi_t61_591133442051411133755680859, phi_t61_591133442051411133755680860, phi_t61_591133442051411133755680861, phi_t61_591133442051411133755680862, phi_t61_591133442051411133755680863, phi_t61_591133442051411133755680864, phi_t61_591133442051411133755680865, phi_t61_591133442051411133755680866, phi_t61_591133442051411133755680867, phi_t61_591133442051411133755680868, phi_t61_591133442051411133755680869, phi_t61_591133442051411133755680870, phi_t61_591133442051411133755680871, phi_t61_591133442051411133755680872, phi_t61_591133442051411133755680873, phi_t61_591133442051411133755680874, phi_t61_591133442051411133755680875, phi_t61_591133442051411133755680876, phi_t61_591133442051411133755680877, phi_t61_591133442051411133755680878, phi_t61_591133442051411133755680879, phi_t61_591133442051411133755680880, phi_t61_591133442051411133755680881, phi_t61_591133442051411133755680882, phi_t61_591133442051411133755680883, phi_t61_591133442051411133755680884, phi_t61_591133442051411133755680885, phi_t61_591133442051411133755680886, phi_t61_591133442051411133755680887, phi_t61_591133442051411133755680888, phi_t61_591133442051411133755680889, phi_t61_591133442051411133755680890, phi_t61_591133442051411133755680891, phi_t61_591133442051411133755680892, phi_t61_591133442051411133755680893, phi_t61_591133442051411133755680894, phi_t61_1182266884102822267511361601, phi_t61_1182266884102822267511361602, phi_t61_1182266884102822267511361603, phi_t61_1182266884102822267511361604, phi_t61_1182266884102822267511361605, phi_t61_1182266884102822267511361606, phi_t61_1182266884102822267511361607, phi_t61_1182266884102822267511361608, phi_t61_1182266884102822267511361609, phi_t61_1182266884102822267511361610, phi_t61_1182266884102822267511361611, phi_t61_1182266884102822267511361612, phi_t61_1182266884102822267511361613, phi_t61_1182266884102822267511361614, phi_t61_1182266884102822267511361615, phi_t61_1182266884102822267511361616, phi_t61_1182266884102822267511361617, phi_t61_1182266884102822267511361618, phi_t61_1182266884102822267511361619, phi_t61_1182266884102822267511361620, phi_t61_1182266884102822267511361621, phi_t61_1182266884102822267511361622, phi_t61_1182266884102822267511361623, phi_t61_1182266884102822267511361624, phi_t61_1182266884102822267511361625, phi_t61_1182266884102822267511361626, phi_t61_1182266884102822267511361627, phi_t61_1182266884102822267511361628, phi_t61_1182266884102822267511361629, phi_t61_1182266884102822267511361630, phi_t61_1182266884102822267511361631, phi_t61_1182266884102822267511361632, phi_t61_1182266884102822267511361633, phi_t61_1182266884102822267511361634, phi_t61_1182266884102822267511361635, phi_t61_1182266884102822267511361636, phi_t61_1182266884102822267511361637, phi_t61_1182266884102822267511361638, phi_t61_1182266884102822267511361639, phi_t61_1182266884102822267511361640, phi_t61_1182266884102822267511361641, phi_t61_1182266884102822267511361642, phi_t61_1182266884102822267511361643, phi_t61_1182266884102822267511361644, phi_t61_1182266884102822267511361645, phi_t61_1182266884102822267511361646, phi_t61_1182266884102822267511361647, phi_t61_1182266884102822267511361648, phi_t61_1182266884102822267511361649, phi_t61_1182266884102822267511361650, phi_t61_1182266884102822267511361651, phi_t61_1182266884102822267511361652, phi_t61_1182266884102822267511361653, phi_t61_1182266884102822267511361654, phi_t61_1182266884102822267511361655, phi_t61_1182266884102822267511361656, phi_t61_1182266884102822267511361657, phi_t61_1182266884102822267511361658, phi_t61_1182266884102822267511361659, phi_t61_1182266884102822267511361660, phi_t61_1182266884102822267511361661, phi_t61_1182266884102822267511361662, phi_t61_1182266884102822267511361663, phi_t61_1182266884102822267511361664, phi_t61_1182266884102822267511361665, phi_t61_1182266884102822267511361666, phi_t61_1182266884102822267511361667, phi_t61_1182266884102822267511361668, phi_t61_1182266884102822267511361669, phi_t61_1182266884102822267511361670, phi_t61_1182266884102822267511361671, phi_t61_1182266884102822267511361672, phi_t61_1182266884102822267511361673, phi_t61_1182266884102822267511361674, phi_t61_1182266884102822267511361675, phi_t61_1182266884102822267511361676, phi_t61_1182266884102822267511361677, phi_t61_1182266884102822267511361678, phi_t61_1182266884102822267511361679, phi_t61_1182266884102822267511361680, phi_t61_1182266884102822267511361681, phi_t61_1182266884102822267511361682, phi_t61_1182266884102822267511361683, phi_t61_1182266884102822267511361684, phi_t61_1182266884102822267511361685, phi_t61_1182266884102822267511361686, phi_t61_1182266884102822267511361687, phi_t61_1182266884102822267511361688, phi_t61_1182266884102822267511361689, phi_t61_1182266884102822267511361690, phi_t61_1182266884102822267511361691, phi_t61_1182266884102822267511361692, phi_t61_1182266884102822267511361693, phi_t61_1182266884102822267511361694]

def diagonalPincerCertificateScalesThroughT61 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61]

def diagonalPincerKillDepthThroughT61 : ℕ → ℕ
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
  | _ => 0

/-- All 27 imported scales through t=61 fire. -/
theorem certifiedKill_diagonal_all_imported_through_t61 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT61,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT61 t) := by
  intro t ht
  simp only [diagonalPincerCertificateScalesThroughT61, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t17
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t19
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t23
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t25
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t27
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t29
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t31
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t32
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t37
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t41
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t43
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t47
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t49
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t53
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t59
  · simpa [diagonalPincerKillDepthThroughT61] using certifiedKill_diagonal_t61

#print axioms certifiedKill_diagonal_all_imported_through_t61

end TotientTailPeriodKiller
end Erdos249257
